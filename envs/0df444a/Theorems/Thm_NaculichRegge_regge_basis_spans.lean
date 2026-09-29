-- Prove2me | Theorems.Thm_NaculichRegge_regge_basis_spans
-- name    : NaculichRegge.regge_basis_spans
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:23:29.898292+00:00
-- url     : https://prove2.me/theorems/1bcf228e-42a0-41fd-a82a-02c79a20a393
-- title:
--   The Regge basis spans all Regge-limit amplitudes obeying the group-theory constraints
-- statement:
--   Let $\ell\ge2$. If complex numbers $A_1,\dots,A_{3\ell+3}$ satisfy the four $\ell$-loop group-theory constraints $\sum_\lambda r^{(\ell)}_\lambda A_\lambda=0$ (eq. (2.5) with the null vectors (2.10)/(2.12), extended by prepending zeros) and $A_2=0$ (the Regge limit), then there are coefficients $B_{ik}$ such that $A_\lambda$ is the $\lambda$-th extended-trace coordinate of $\sum_{(i,k)}B_{ik}N^{\ell-i}C_{ik}$ for all $1\le\lambda\le3\ell+3$.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 10–11, 14; Sec. 4 opening paragraphs, footnote 6

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, Sec. 4 (opening paragraphs and footnote 6): for `ℓ ≥ 2`, every assignment of
`ℓ`-loop colour-ordered amplitudes `A_1, …, A_{3ℓ+3}` that obeys the four group-theory
constraints and has `A_2 = 0` (the Regge limit) is the coordinate vector of
`∑ B_{ik} N^{ℓ−i} C_{ik}` for some coefficients `B_{ik}`. -/
theorem regge_basis_spans (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (a : ℕ → ℂ)
    (hnull : ∀ r : Fin 4, ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3), nullVector ℓ r lam * a lam = 0)
    (h2 : a 2 = 0) :
    ∃ B : ℕ × ℕ → ℂ, ∀ lam ∈ Finset.Icc 1 (3 * ℓ + 3),
      a lam = extCoord ℓ (reggeAmplitude ℓ B) lam := by sorry

end NaculichRegge
