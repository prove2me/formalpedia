-- Prove2me | Theorems.Thm_OLPRegret_eq_39
-- name    : OLPRegret.eq_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:30.107675+00:00
-- url     : https://prove2.me/theorems/2e008aa2-2348-42ab-a314-4ea7affca66f
-- title:
--   (39) — the regret against the linear program is at least the sum of myopic regrets
-- statement:
--   Let $\delta>0$ with $\delta\iota\le\beta$, and let $\alpha$ bound the bundles. For every non-anticipating policy, every sample with $u_s,a_s\ge0$, $a_s\le\alpha$, and every choice of shadow prices,
--   $$
--   \underline R_n=\bar V_n^\beta-v_n\ge\sum_{t=\lceil2\|\alpha\|/\delta\rceil}^nr_t,
--   $$
--   where $r_t$ is the lower myopic regret. The bound is what turns per-period errors into regret.
--
--   Differences from the source:
--   - generalization: the optimal policy → every non-anticipating policy; reason: the derivation uses only (28)–(30), valid for any feasible action, and (14) is such a policy
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: $y_0$ undefined at $t=1$ → $y_0=0$; reason: (30) at $t=1$ reads $xa'y_0\le 0$ for every bundle, which forces $y_0=0$
--   - encoding: (39) for the random customers, which satisfy Assumptions 2 and 4 almost surely → pathwise for every sample with $u_s,a_s\ge0$, $a_s\le\alpha$; reason: samples violating those bounds are null
--   - encoding: periods counted backward, $t=n,\dots,1$ → the index $t$ of `Fin n` holds period $t+1$, and the stock $tb_t$ is tracked with $b_t$ recovered by division; reason: Lean convention; same instances
-- source:
--   Bray, arXiv:1912.08917v6, (39), p.32; derivation pp.31–32

import Mathlib
import Definitions.Def_OLPRegret_regret
import Definitions.Def_OLPRegret_myopicRegret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, (39), p.32: for `δ > 0` with `δι ≤ β`, pathwise,
`R̲ₙ ≥ Σ_{t=⌈2‖α‖/δ⌉}^n rₜ`.

**Formalization Note** `rₜ` is `rLower`. The page derives this for the optimal policy; the derivation
uses only (28)–(30), valid for any feasible action, so it is stated for every non-anticipating
policy, every sample of customers with `0 ≤ uₛ`, `0 ≤ aₛ ≤ α`, and every choice `Y` of shadow
prices. -/
theorem eq_39 {m n : ℕ} (β : E m) (hβ : VNonneg β) (α : E m) (hα : VNonneg α) (δ : ℝ) (hδ : 0 < δ)
    (hδβ : ∀ i, δ ≤ β i) (π : Policy m n) (ω : Sample m n)
    (hω : ∀ s, 0 ≤ (ω s).1 ∧ VNonneg (ω s).2 ∧ VLe (ω s).2 α)
    (Y : ℕ → E m → E m) (hY : IsShadowPriceChoice ω Y) :
    ∑ t : Fin n with ⌈2 * ‖α‖ / δ⌉₊ ≤ period t, rLower δ π.scheme β Y ω t ≤
      offlineLP ω β - onlineValue π.scheme β ω := by sorry

end OLPRegret
