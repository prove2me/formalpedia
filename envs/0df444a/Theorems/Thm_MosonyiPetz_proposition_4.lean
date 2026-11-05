-- Prove2me | Theorems.Thm_MosonyiPetz_proposition_4
-- name    : MosonyiPetz.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:56.167729+00:00
-- url     : https://prove2.me/theorems/898a6575-616e-4c11-87aa-6fb567d0d6a8
-- title:
--   Proposition 4: $u=\sum_iv_i\otimes w_i\otimes E_{\sigma(i)i}$
-- statement:
--   Let $d,m,K\in\mathbb N$ and let $\mathcal A=\{\sum_{i=1}^KA_i\otimes I_m\otimes E_{ii}:A_i\in M_d\}\subset M_d\otimes M_m\otimes M_K$, the algebra $\bigoplus_{j=1}^KM_d$ with all multiplicities $m$ and all dimensions $d$ (p.7). If $u$ is a unitary such that $a\mapsto u^*au$ maps $\mathcal A$ into $\mathcal A$, then there are a permutation $\sigma$ of $\{1,\dots,K\}$ and unitaries $v_i\in M_d$, $w_i\in M_m$ with
--
--   $$u=\sum_{i=1}^Kv_i\otimes w_i\otimes E_{\sigma(i)i}.$$
--
--   Applied to $u=P_{m,d}T(D_1)^{it}$, continuity in $t$ forces $\sigma=\mathrm{id}$, which splits $T(D_1)$ into tensor factors (p.9).
--
--   **Formalization Note** Tensor products are Kronecker products on `(Fin d × Fin m) × Fin K`; $E_{\sigma(i)i}$ is `Matrix.single (σ i) i 1`.
--
--   Differences from the source:
--   - encoding: u*Au ⊂ A for the unitary u → u ∈ Matrix.unitaryGroup and ∀ a ∈ A, star u * a * u ∈ A; reason: same condition
--   - encoding: the case when all multiplicities and dimensions are the same, A ⊂ M_d ⊗ M_m ⊗ M_K in the coordinates of p.7 → blockAlgebra d m K = {Σ_i (A_i ⊗ₖ 1) ⊗ₖ single i i 1} on (Fin d × Fin m) × Fin K; reason: the paper's own coordinates; {1, …, K} is Fin K
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §3, p.8, Proposition 4 (setting p.7)

import Mathlib
import Definitions.Def_MosonyiPetz_blockAlgebra

open scoped Matrix Kronecker

namespace MosonyiPetz

/-- **Proposition 4: unitaries normalizing ⊕_K M_d ⊗ I_m.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §3, p.8, Proposition 4: "In the case when all the multiplicities and all the dimensions are
the same, u must be of the form u = Σ_{i=1}^K vi ⊗ wi ⊗ E_{σ(i)i}, where vi ∈ Md and wi ∈ Mm are
unitaries and σ is a permutation of the set {1, 2, . . . , K}." The setting (p.7): "Elements of A
have the form Σ_i Ai ⊗ Im ⊗ Eii, where Ai is an element of Md and {Eij : 1 ≤ i, j ≤ K} are the
standard matrix units of MK."

Let `A = {Σ_i A_i ⊗ I_m ⊗ E_ii}` in `M_d ⊗ M_m ⊗ M_K` and let `u` be a unitary with
`u* a u ∈ A` for every `a ∈ A`. Then there are a permutation `σ` of `{1, …, K}` and unitaries
`v_i ∈ M_d`, `w_i ∈ M_m` with `u = Σ_i v_i ⊗ w_i ⊗ E_{σ(i) i}`.

**Formalization Note.** Tensor products are Kronecker products on the index type
`(Fin d × Fin m) × Fin K`; `E_{σ(i) i}` is `Matrix.single (σ i) i 1`; `{1, …, K}` is `Fin K`. -/
theorem proposition_4 (d m K : ℕ)
    (u : Matrix ((Fin d × Fin m) × Fin K) ((Fin d × Fin m) × Fin K) ℂ)
    (hu : u ∈ Matrix.unitaryGroup ((Fin d × Fin m) × Fin K) ℂ)
    (hinv : ∀ a ∈ blockAlgebra d m K, star u * a * u ∈ blockAlgebra d m K) :
    ∃ (σ : Equiv.Perm (Fin K)) (v : Fin K → Matrix.unitaryGroup (Fin d) ℂ)
      (w : Fin K → Matrix.unitaryGroup (Fin m) ℂ),
      u = ∑ i, ((v i : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (w i : Matrix (Fin m) (Fin m) ℂ)) ⊗ₖ
        Matrix.single (σ i) i (1 : ℂ) := by sorry

end MosonyiPetz
