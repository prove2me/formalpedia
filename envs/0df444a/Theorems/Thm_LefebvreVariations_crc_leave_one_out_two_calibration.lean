-- Prove2me | Theorems.Thm_LefebvreVariations_crc_leave_one_out_two_calibration
-- name    : LefebvreVariations.crc_leave_one_out_two_calibration
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:26:51.16205+00:00
-- url     : https://prove2.me/theorems/57817678-a118-4b7a-aab9-c136040f0867
-- title:
--   Lefebvre's variations, No. 273 — on a theme by Angelopoulos, Bates, Fisch, Lei and Schuster: conformal risk control with two calibration points on a four-point grid, leave-one-out form
-- statement:
--   Let $\Lambda=\{0,1,2,3\}$, let $B,\alpha\in\mathbb R$, and let $L_0,L_1,L_2:\Lambda\to\mathbb R$ be non-increasing with $L_i(\lambda)\le B$ for all $\lambda\in\Lambda$ and $L_i(3)\le\alpha$. For each $i\in\{0,1,2\}$, with $\{j,k\}=\{0,1,2\}\setminus\{i\}$, put
--   $$
--   \hat\lambda_{(i)}=\min\Bigl\{\lambda\in\Lambda:\ \tfrac{1}{3}\bigl(L_j(\lambda)+L_k(\lambda)\bigr)+\tfrac{B}{3}\le\alpha\Bigr\},
--   $$
--   with $\hat\lambda_{(i)}=3$ if the set is empty. Then
--   $$
--   \sum_{i=0}^{2} L_i\bigl(\hat\lambda_{(i)}\bigr)\ \le\ 3\alpha ,
--   \qquad\text{i.e.}\qquad \frac13\sum_{i=0}^{2}L_i(\hat\lambda_{(i)})\le\alpha .
--   $$
--
--   In conformal risk control one calibrates a parameter $\hat\lambda$ on $n$ exchangeable monotone losses so that the expected loss of the next, exchangeable loss at $\hat\lambda$ is at most $\alpha$. When the three losses are uniformly permuted, that expectation is exactly the average over the three leave-one-out choices above, so this is the case $n=2$ of the key inequality on a four-point parameter grid, for arbitrary (not random) loss functions.
--
--   **Formalization Note** The parameter is the parent's `ConformalRiskControl.lhat` (imported from the parent's definitions) on the set `Λ = {0, 1, 2, 3} : Set ℝ`, with the two calibration losses `fun j : Fin 2 => L (i.succAbove j)` obtained by removing index `i`. No sign condition is imposed on the losses, and right-continuity is automatic on a finite grid. `lhat` is the infimum of the set (a minimum here) and equals `sSup Λ = 3` when the set is empty.
--
--   **Why this is a variation.** A variation on the open platform problem ConformalRiskControl.risk_control_upper_bound (Theorem 1 of Conformal Risk Control: E[L_{n+1}(lhat)] <= alpha for exchangeable monotone losses), played at n = 2 on a four-point parameter grid and in the deterministic leave-one-out form that the exchangeability argument reduces to. It uses the parent's own definitions (`lhat`). It is not a formal consequence of the parent, which is a statement about random exchangeable losses on a general compact parameter set.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814 (identity of the paper and its Theorem 1, the expected-loss guarantee for exchangeable monotone losses, confirmed; section and theorem numbering cited from memory). The leave-one-out inequality is the combinatorial core of the exchangeability argument (the author's reading, cited from memory). Checked here by hand (the full-sample parameter is no larger than each leave-one-out parameter because the losses are at most B; then monotonicity) and by exact rational arithmetic: exhaustively over all non-increasing integer-valued loss triples on the four-point grid with values in {-1,0,1,2}, B in {-1..3}, alpha in {-2..2} (245295 cases), and on 300000 random rational instances; the maximum of the left side minus 3*alpha is 0, so the bound is attained.

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

set_option autoImplicit false

namespace LefebvreVariations

open ConformalRiskControl

/-- Conformal risk control with `n = 2` calibration points, in its exchangeability-free (leave-one-out) form on the four-point grid `Λ = {0, 1, 2, 3}`.
The calibration parameter `λ̂` of eq. (4) of Angelopoulos–Bates–Fisch–Lei–Schuster, *Conformal Risk Control*, arXiv:2208.02814, is computed from every pair of the three non-increasing losses `L 0, L 1, L 2`; the average over the three leave-one-out choices of the loss of the left-out point is at most `α`. The average over the three choices is the expected test loss when the three losses are exchangeable.
Source: Angelopoulos, Bates, Fisch, Lei, Schuster, *Conformal Risk Control*, Theorem 1 (theorem number cited from memory). -/
theorem crc_leave_one_out_two_calibration (B α : ℝ) (L : Fin 3 → ℝ → ℝ)
    (hanti : ∀ i, AntitoneOn (L i) ({0, 1, 2, 3} : Set ℝ))
    (hbd : ∀ i, ∀ x ∈ ({0, 1, 2, 3} : Set ℝ), L i x ≤ B)
    (hend : ∀ i, L i 3 ≤ α) :
    ∑ i : Fin 3, L i (lhat ({0, 1, 2, 3} : Set ℝ) B α (fun j : Fin 2 => L (i.succAbove j)))
      ≤ 3 * α := by
  sorry

end LefebvreVariations
