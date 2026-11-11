-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_proposition_3_5
-- name    : IIDMultiItem.TwoPoint.proposition_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:58:34.40918+00:00
-- url     : https://prove2.me/theorems/3e07d21d-bba0-45f5-998e-5b86374398f1
-- title:
--   Proposition 3.5 — for integer reserves with θ_0 = 0 and 0 ≤ θ_d ≤ d the auction is deterministic, feasible, DSIC, ex-post IR, with nonnegative payments
-- statement:
--   Let $0<a<b$ and $0<p<1$. For every choice of integer reserves $\theta_0,\dots,\theta_m$ with $\theta_0=0$ and $0\le\theta_d\le d$, the auction of §3.2 (exclusive-count ranking with priority $1<\dots<n$, allocation and payments (3.4)) is
--   * deterministic: $x_{ij}(S)\in\{0,1\}$;
--   * feasible: $x_{ij}(S)\in[0,1]$ and $\sum_i x_{ij}(S)\le1$;
--   * DSIC and ex-post IR (2.2) on the two-point type space;
--   * with nonnegative payments: $s_i(S)\ge0$ at every profile.
--
--   The reserves (3.2) satisfy the hypotheses, so this gives the truthfulness half of Theorem 3.3.
--
--   Differences from the source:
--   - encoding: integer reserves θ_0, …, θ_m with θ_0 = 0 and 0 ≤ θ_d ≤ d → θ : ℕ → ℤ with θ 0 = 0 and 0 ≤ θ d ≤ d for 1 ≤ d ≤ m; reason: values beyond m are never used; the constraint is imposed exactly on θ_0, …, θ_m (for d = 0 it is θ_0 = 0)
--   - encoding: types t ∈ {a, b}^m → types S : Finset (Fin m); reason: the identification of Section 3
--   - generalization: n, m ≥ 1 (§2.1: n buyers, items [m] for a positive integer m) → any n, m ∈ ℕ; reason: at n = 0 every clause quantifies over no buyer; at m = 0 every allocation is empty and Θ_i ≥ θ_0 = 0 makes every payment 0; for n, m ≥ 1 it is the paper's statement
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 15 (PDF 17), Proposition 3.5

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Counts
import Definitions.Def_IIDMultiItem_TwoPoint_Auction

namespace IIDMultiItem.TwoPoint

/-- Proposition 3.5. For every choice of integer reserves with `θ_0 = 0` and `0 ≤ θ_d ≤ d`, the
auction is deterministic, feasible, DSIC and ex-post IR, with nonnegative payments. -/
theorem proposition_3_5 (n m : ℕ) (a b p : ℝ) (ha : 0 < a) (hab : a < b) (hp0 : 0 < p)
    (hp1 : p < 1) (θ : ℕ → ℤ) (hθ0 : θ 0 = 0)
    (hθ : ∀ d : ℕ, 1 ≤ d → d ≤ m → 0 ≤ θ d ∧ θ d ≤ (d : ℤ)) :
    (auction a b θ : Mechanism (Finset (Fin m)) n m).Deterministic ∧
    (auction a b θ : Mechanism (Finset (Fin m)) n m).Feasible ∧
    (auction a b θ : Mechanism (Finset (Fin m)) n m).DSIC_IR (twoPoint a b p m) ∧
    ∀ (S : Fin n → Finset (Fin m)) (i : Fin n),
      0 ≤ (auction a b θ : Mechanism (Finset (Fin m)) n m).s S i := by sorry

end IIDMultiItem.TwoPoint
