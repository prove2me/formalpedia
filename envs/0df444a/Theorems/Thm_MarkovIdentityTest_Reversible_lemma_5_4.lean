-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_5_4
-- name    : MarkovIdentityTest.Reversible.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:31.128568+00:00
-- url     : https://prove2.me/theorems/6572041b-22c0-4d69-bc04-53d128548cef
-- title:
--   Lemma 5.4 — the linear clipping error costs $\le 22$ per reached row: $(L-1)F+\frac{2(L-1)}{L}\mathrm{Lin}_L\ge\frac12FN-\mathrm{Rem}$
-- statement:
--   Consider a stopped row with the law (5.1) (reached with probability $\rho=\Pr(N\ge1)$, return probability $s\in[0,1)$, laws $r,e$, row law $q=sr+(1-s)e$, retained length $L$, and $N=L+1$ when the row is reached). Let $0\le F\le4$ and coefficients $\kappa_y\in[-1,3]$ with $\sum_yq_y\kappa_y^2\le4F$; put $\bar\kappa=\kappa-\mathbb E_q\kappa$ and $\mathrm{Lin}_l=\sum_{b\le l}\bar\kappa_{Y_b}$. Then there is a nonnegative random variable $\mathrm{Rem}$, a function of the row's stopped data, such that
--   $$(L-1)F+\frac{2(L-1)}{L}\mathrm{Lin}_L\ge\tfrac12FN-\mathrm{Rem},\qquad\mathbb E\,\mathrm{Rem}\le22\Pr(N\ge1),$$
--   where the left side is $0$ when $L=0$. (Off the reached event $N=L=0$ and $\mathrm{Rem}=0$.)
--
--   Differences from the source:
--
--   - generalization: one row of a chain at a geometric time → any stopped row with law (5.1) (s ∈ [0, 1), r, e, ρ); reason: as for Lemma 5.1: the proof uses only (5.1); chain rows are an instance by Eq. (5.1)
--   - generalization: a nonnegative random variable Rem_i → a nonnegative function of the reached row's outcome (L, Y_1, …, Y_N), 0 off the reached event; reason: a narrower class of witnesses makes the existence claim stronger; the paper's Rem_i is such a function
--   - encoding: E Rem_i → ρ × (series against the law (5.1)) with absolute convergence asserted; reason: Rem = 0 off the reached event
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 28, Lemma 5.4 (setup paragraph p. 28)

import Mathlib
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

namespace MarkovIdentityTest.Reversible

/-- Lemma 5.4 (Jia, p. 28 / PDF 30), for one abstract stopped row with the law (5.1) (return
probability `s`, returning law `r`, final law `e`, row law `q = s r + (1 - s) e`, reach
probability `ρ = Pr(N ≥ 1)`), and the setup of §5.3: `0 ≤ F ≤ 4`, `κ_y ∈ [-1, 3]`,
`∑ q κ² ≤ 4F`. On a reached outcome `N = L + 1`; off it `L = N = 0` and `Rem = 0`. -/
theorem lemma_5_4 {α : Type*} [Fintype α] (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (r e : α → ℝ) (hr : ∀ y, 0 ≤ r y) (hr1 : ∑ y, r y = 1) (he : ∀ y, 0 ≤ e y)
    (he1 : ∑ y, e y = 1) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : ℝ) (κ : α → ℝ) (hF0 : 0 ≤ F) (hF4 : F ≤ 4) (hκ : ∀ y, -1 ≤ κ y ∧ κ y ≤ 3)
    (hκF : ∑ y, rowMixture s r e y * κ y ^ 2 ≤ 4 * F) :
    ∃ Rem : (l : ℕ) → (Fin (l + 1) → α) → ℝ,
      (∀ (l : ℕ) (y : Fin (l + 1) → α), 0 ≤ Rem l y) ∧
      (∀ (l : ℕ) (y : Fin (l + 1) → α), (1 / 2) * F * ((l : ℝ) + 1) - Rem l y ≤
        (if l = 0 then 0 else
          ((l : ℝ) - 1) * F + 2 * ((l : ℝ) - 1) / l * linCorrection (rowMixture s r e) κ l y)) ∧
      StoppedRowIntegrable s r e Rem ∧
      ρ * stoppedRowExp s r e Rem ≤ 22 * ρ := by sorry

end MarkovIdentityTest.Reversible
