-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcgPairs_decompose
-- name    : LimitedBFGS.SQN.pcgPairs_decompose
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T20:53:45.267554+00:00
-- url     : https://prove2.me/theorems/66174e1f-4be5-4c50-a6a9-27b8c73b44d8
-- title:
--   Splitting the retained PCG pair window into its old part and the newest pair
-- statement:
--   Let $x_k$ be the iterate of the preconditioned conjugate gradient method with fixed preconditioner $H_0$ on a quadratic with exact line searches, and let $(s_j, y_j)$ be the consecutive difference pair $s_j = x_{j+1} - x_j$, $y_j = g(x_{j+1}) - g(x_j)$.
--
--   Define the list
--   $$P_k = \operatorname{trim}_m\big(P_{k-1} \mathbin{+\!\!+} [(s_{k-1}, y_{k-1})]\big), \qquad P_0 = [],$$
--   where $\operatorname{trim}_m$ drops the oldest entries until at most $m$ remain. This is exactly the window of pairs that the limited-storage iteration of Nocedal (17) stores, but fed from the PCG iterates instead.
--
--   **Claim.** (i) Every pair retained in $P_k$ is $(s_j, y_j)$ for some $j < k$. (ii) If $m \ge 1$ then
--   $$P_{k+1} = \operatorname{drop}_{\,|P_k| + 1 - m}(P_k) \mathbin{+\!\!+} [(s_k, y_k)],$$
--   so the pair just appended always survives the trim and sits at the end.
--
--   **Why.** (i) is induction on $k$: membership in the trimmed list implies membership in $P_k \mathbin{+\!\!+} [(s_{k-1},y_{k-1})]$, which by the induction hypothesis is either an older pair or the newest one. (ii) The trim index is $|P_k| + 1 - m$, which is at most $|P_k|$ because $m \ge 1$; the lemma $(l_1 + l_2).\,drop\,i = l_1.\,drop\,i + l_2$ then splits the drop across the old window and the singleton.
--
--   **Role.** This is the bookkeeping needed to compare the limited-storage BFGS matrix built from the stored pairs with the conjugate gradient recurrence (Nocedal 1980, p. 778).
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, iteration (17): the new pair is appended and the oldest one dropped once more than m are stored.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs

open Matrix

namespace LimitedBFGS.SQN

/-- Bookkeeping for the shadow list of PCG correction pairs. `pcgPairs` is the
append-and-drop of the SQN iteration driven by `pcgIter`; two facts describe it. First, every
retained pair is the shadow pair of some index strictly below the current one. Second, when
`1 ≤ m`, the successor window is the drop of the old window at `old.length + 1 - m`
followed by the newest pair, so the trim never discards the pair just appended. -/
theorem pcgPairs_decompose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (∀ p ∈ pcgPairs A b H₀ x₀ m k, ∃ j < k, p = pcgPair A b H₀ x₀ j) ∧
      pcgPairs A b H₀ x₀ m (k + 1) =
        (pcgPairs A b H₀ x₀ m k).drop ((pcgPairs A b H₀ x₀ m k).length + 1 - m) ++
          [pcgPair A b H₀ x₀ k] := by sorry

end LimitedBFGS.SQN
