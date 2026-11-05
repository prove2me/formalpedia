-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_exists_real_orthogonal_diagonalization
-- name    : FowlerLSQC.Canonical.exists_real_orthogonal_diagonalization
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:31.953566+00:00
-- url     : https://prove2.me/theorems/fcc2c3e4-606d-4359-a21d-b8e7c0feadeb
-- title:
--   $\tilde G_S^T\tilde G_S$ is diagonalized by a real special orthogonal $\tilde O_1$
-- statement:
--   Let $G_S\in SU(4)$ be a two-qubit gate of determinant one and let $\tilde G_S=Q^\dagger G_S Q$ be its matrix in the magic basis. Then there are a real special orthogonal matrix $\tilde O_1\in SO(4)$ and real numbers $\epsilon_1,\epsilon_2,\epsilon_3,\epsilon_4$ with $\epsilon_1+\epsilon_2+\epsilon_3+\epsilon_4=0$ such that
--   $$
--   \tilde G_S^T\tilde G_S=\tilde O_1^T\,\mathrm{diag}\big(e^{2i\epsilon_1},e^{2i\epsilon_2},e^{2i\epsilon_3},e^{2i\epsilon_4}\big)\,\tilde O_1 .
--   $$
--   Here ${}^T$ is the transpose, without complex conjugation. In words: the symmetric unitary matrix $\tilde G_S^T\tilde G_S$ has a real orthonormal eigenbasis (the rows of $\tilde O_1$), which can be oriented to have determinant one, and its eigenphases can be chosen to sum to zero.
--
--   This is the first step of the construction of a canonical decomposition: $\tilde O_1$ becomes the first layer of single-qubit gates, and the $\epsilon_k$ determine the non-local parameters.
--
--   **Formalization Note** $\tilde O_1$ is an element of `Matrix.specialOrthogonalGroup (Fin 4) ℝ` mapped entrywise into $\mathbb C$; the magic basis is indexed by `Fin 4`, and `eps 0` is $\epsilon_1$.
--
--   Differences from the source:
--   - encoding: $\epsilon_1,\dots,\epsilon_4$ and the magic basis indexed $1,\dots,4$ → indexed by `Fin 4` from $0$; reason: Lean convention, same instances.
--   - encoding: "real, orthonormal eigenbasis" with $\det\tilde O_1=1$ → $\tilde O_1$ is the entrywise complex cast of a matrix in `Matrix.specialOrthogonalGroup (Fin 4) ℝ`; reason: a complex matrix is real orthogonal of determinant one exactly when it is such a cast.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.3, (4.5)–(4.6), pp.49–50 (PDF pp.67–68)

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_magicQ
open scoped Matrix

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.3,
(4.5)–(4.6), pp.49–50 (PDF pp.67–68): for `G_S ∈ SU(4)` and `G̃_S = Q† G_S Q`, the symmetric
matrix `G̃_Sᵀ G̃_S` has a real orthonormal eigenbasis, which can be taken with determinant 1:
there are `Õ1 ∈ SO(4)` (real) and `ε1, …, ε4 ∈ ℝ` with `ε1 + ε2 + ε3 + ε4 = 0` such that
`G̃_Sᵀ G̃_S = Õ1ᵀ G̃_{2ε} Õ1`, `G̃_{2ε} = diag(e^{2iε1}, …, e^{2iε4})`.

**Formalization Note.** `ᵀ` is the plain transpose (no conjugation). `Õ1` (`O1t`) is a real
special orthogonal matrix (`Matrix.specialOrthogonalGroup (Fin 4) ℝ`) cast entrywise to `ℂ`; its
rows are the eigenvectors. `ε` is `eps : Fin 4 → ℝ`, `eps 0` the book's `ε1`. The sum `0` is the
normalization the book reaches by shifting the `ε_k` by multiples of `π` (which leaves
`e^{2iε_k}` unchanged). -/
theorem exists_real_orthogonal_diagonalization
    (GS : Matrix (Bool × Bool) (Bool × Bool) ℂ) (hGS : GS ∈ Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    ∃ O1t ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ, ∃ eps : Fin 4 → ℝ,
      ∑ k, eps k = 0 ∧
      (magicQᴴ * GS * magicQ)ᵀ * (magicQᴴ * GS * magicQ) =
        (O1t.map (fun x : ℝ => (x : ℂ)))ᵀ *
          Matrix.diagonal (fun k => Complex.exp (2 * (eps k : ℂ) * Complex.I)) *
          O1t.map (fun x : ℝ => (x : ℂ)) := by sorry

end FowlerLSQC.Canonical
