-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_O2_special_orthogonal
-- name    : FowlerLSQC.Canonical.O2_special_orthogonal
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:34.218375+00:00
-- url     : https://prove2.me/theorems/ad7af9d3-2441-4e52-918f-627d0828c7a4
-- title:
--   $\tilde O_2=\tilde G_S\tilde O_1^T\tilde G_{\vec\epsilon}^*$ is special orthogonal
-- statement:
--   Let $G_S\in SU(4)$, $\tilde G_S=Q^\dagger G_S Q$, and suppose $\tilde O_1\in SO(4)$ (real) and $\epsilon_1,\dots,\epsilon_4\in\mathbb R$ with $\sum_k\epsilon_k=0$ satisfy
--   $$
--   \tilde G_S^T\tilde G_S=\tilde O_1^T\,\mathrm{diag}\big(e^{2i\epsilon_1},\dots,e^{2i\epsilon_4}\big)\,\tilde O_1 .
--   $$
--   Let $\tilde G_{\vec\epsilon}=\mathrm{diag}(e^{i\epsilon_1},\dots,e^{i\epsilon_4})$ and
--   $$
--   \tilde O_2=\tilde G_S\,\tilde O_1^T\,\tilde G_{\vec\epsilon}^{\,*},
--   $$
--   where ${}^*$ is entrywise complex conjugation. Then $\tilde O_2$ is a real special orthogonal matrix, and
--   $$
--   \tilde G_S=\tilde O_2\,\tilde G_{\vec\epsilon}\,\tilde O_1 .
--   $$
--   This produces the second layer of single-qubit gates of the canonical decomposition: after conjugation by $Q$, both $\tilde O_1$ and $\tilde O_2$ become tensor products of single-qubit gates.
--
--   **Formalization Note** The hypotheses are the data the construction has produced at this point, including $\sum_k\epsilon_k=0$. "Special orthogonal" is stated as equality with the entrywise complex cast of a matrix in `Matrix.specialOrthogonalGroup (Fin 4) ℝ`.
--
--   Differences from the source:
--   - encoding: $\epsilon_1,\dots,\epsilon_4$ and the magic basis indexed $1,\dots,4$ → indexed by `Fin 4` from $0$; reason: Lean convention, same instances.
--   - encoding: "$\tilde O_2$ is special orthogonal" → $\tilde O_2$ equals the complex cast of some real matrix in `Matrix.specialOrthogonalGroup (Fin 4) ℝ`; reason: the book's $SO(4)$ is the real group, as in its use of $\tilde O_1$.
--   - reading: $\tilde G^*_{\vec\epsilon}$ → entrywise complex conjugate `map (starRingEnd ℂ)`; reason: the chapter uses ${}^*$ for complex conjugation (e.g. (4.5), (4.7)).
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.3, p.50 (PDF p.68)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_magicQ
open scoped Matrix

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.3, p.50
(PDF p.68): in the situation of (4.6) — `G_S ∈ SU(4)`, `G̃_S = Q† G_S Q`, `Õ1` real special
orthogonal and `ε ∈ ℝ⁴` with `Σ_k ε_k = 0` and `G̃_Sᵀ G̃_S = Õ1ᵀ G̃_{2ε} Õ1` — let
`G̃_ε = diag(e^{iε1}, …, e^{iε4})` and `Õ2 = G̃_S Õ1ᵀ G̃*_ε`. Then `Õ2` is special orthogonal (a
real orthogonal matrix of determinant 1) and `G̃_S = Õ2 G̃_ε Õ1`.

**Formalization Note.** `ᵀ` is the plain transpose and `G̃*_ε` the entrywise complex conjugate
(`map (starRingEnd ℂ)`). "Special orthogonal" is stated as: `Õ2` equals the entrywise cast of
some `R ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ`. The hypotheses are the invariants the book
has established at this point of the construction, including `Σ ε_k = 0`. -/
theorem O2_special_orthogonal
    (GS : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hGS : GS ∈ Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (O1t : Matrix (Fin 4) (Fin 4) ℝ) (hO1t : O1t ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ)
    (eps : Fin 4 → ℝ) (hsum : ∑ k, eps k = 0)
    (hdiag : (magicQᴴ * GS * magicQ)ᵀ * (magicQᴴ * GS * magicQ) =
      (O1t.map (fun x : ℝ => (x : ℂ)))ᵀ *
        Matrix.diagonal (fun k => Complex.exp (2 * (eps k : ℂ) * Complex.I)) *
        O1t.map (fun x : ℝ => (x : ℂ))) :
    ∃ O2t ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ,
      O2t.map (fun x : ℝ => (x : ℂ)) =
        (magicQᴴ * GS * magicQ) * (O1t.map (fun x : ℝ => (x : ℂ)))ᵀ *
          (Matrix.diagonal (fun k => Complex.exp ((eps k : ℂ) * Complex.I))).map (starRingEnd ℂ) ∧
      magicQᴴ * GS * magicQ =
        O2t.map (fun x : ℝ => (x : ℂ)) *
          Matrix.diagonal (fun k => Complex.exp ((eps k : ℂ) * Complex.I)) *
          O1t.map (fun x : ℝ => (x : ℂ)) := by sorry

end FowlerLSQC.Canonical
