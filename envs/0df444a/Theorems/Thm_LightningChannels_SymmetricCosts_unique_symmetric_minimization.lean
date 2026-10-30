-- Prove2me | Theorems.Thm_LightningChannels_SymmetricCosts_unique_symmetric_minimization
-- name    : LightningChannels.SymmetricCosts.unique_symmetric_minimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:51.437976+00:00
-- url     : https://prove2.me/theorems/ef8b0b70-1abd-4f9f-b1f2-7dd96ff24458
-- title:
--   Proof of Theorem 2(ii), (21): strict convexity and the unique attained symmetric minimum
-- statement:
--   Let $B>0$, $\lambda>0$ and $r>0$. Write $F_r(x,y)=c^{x,y}(\lambda,\lambda)$ for the exact analytic bidirectional cost (3), and let $\alpha=\alpha_+(\lambda,\lambda,r)$. On the full positive real quadrant, $F_r$ is strictly convex. Its value set is nonempty and bounded below. There exists $m>0$ such that
--
--   $$F_r(m,m)\le F_r(x,y)\quad(x,y>0),\qquad
--   \inf_{x,y>0}F_r(x,y)=F_r(m,m).$$
--
--   Every positive pair attaining the global minimum equals $(m,m)$. For every positive real $t$, the diagonal cost is
--
--   $$F_r(t,t)=2t+\frac{2B\alpha^t}{(\alpha^t-1)^2}.$$
--
--   For every positive on-chain transaction cost $C$, equation (21) is retained in full:
--
--   $$F_r(t,t)-\frac{2C\alpha}{(\alpha-1)^2}
--   =2t+\frac{2B\alpha^t}{(\alpha^t-1)^2}-\frac{2C\alpha}{(\alpha-1)^2}.$$
--
--   This supplies attainment and uniqueness missing from the published midpoint comparison, and identifies the published infimum with an actual minimum. Symmetry is a conclusion over the full feasible quadrant.
--
--   Differences from the source:
--   - reading: channel sizes in the unit-payment model → all positive real sizes in the exact analytic cost; reason: the source differentiates the closed-form objective on printed pp. 10–11 / PDF pp. 11–12 and explicitly uses a real solution on printed p. 12 / PDF p. 13; no fractional-barrier stochastic claim is made
--   - encoding: strict convexity and minimization of channel cost minus the on-chain cost → strict convexity and unique attainment of the channel cost, with the full on-chain subtraction retained in (21); reason: the omitted on-chain term is independent of both sizes and changes neither convexity nor minimizers; it is not assumed zero
--   - encoding: the unique minimum is achieved at equal balances → an existential positive diagonal global minimizer, identification of every minimizing pair, and nonempty bounded-below values with their infimum equal to the attained cost; reason: these are explicit representations of unique attainment; no existence or boundedness fact is assumed
-- source:
--   Guasoni, P.; Huberman, G.; Shikhelman, C., Lightning Network Economics: Channels, Management Science, Articles in Advance, published online November 6, 2023, https://doi.org/10.1287/mnsc.2022.01664, §5, Proof of Theorem 2(ii), unique-minimizer passage and equation (21), printed p. 11 / PDF p. 12.

import Definitions.Def_LightningChannels_SymmetricCosts_IsGlobalMin
import Definitions.Def_LNChannels_SmallRate_minSymCost

set_option autoImplicit false

namespace LightningChannels.SymmetricCosts

/-- Proof of Theorem 2(ii), printed p. 11 / PDF p. 12: strict convexity,
unique attained symmetric minimum, and the full diagonal expression (21).
The analytic size domain is all positive reals, as in the source's calculus.
The infimum's nonempty bounded-below value set and its attained value are conclusions.
The diagonal formula retains the on-chain subtraction for every positive transaction cost. -/
theorem unique_symmetric_minimization (B rate r : ℝ)
    (hB : 0 < B) (hRate : 0 < rate) (hr : 0 < r) :
    let a := LNChannels.Exact.alphaPlus rate rate r
    StrictConvexOn ℝ positiveQuadrant
      (fun p : ℝ × ℝ => LNChannels.RateBounds.biCost rate rate r B p.1 p.2) ∧
    ({v : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      LNChannels.RateBounds.biCost rate rate r B x y = v}).Nonempty ∧
    BddBelow {v : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      LNChannels.RateBounds.biCost rate rate r B x y = v} ∧
    (∃ m : ℝ, IsGlobalMin B rate r m m ∧
      (∀ x y : ℝ, IsGlobalMin B rate r x y → x = m ∧ y = m) ∧
      LNChannels.SmallRate.minSymCost rate r B =
        LNChannels.RateBounds.biCost rate rate r B m m) ∧
    (∀ m : ℝ, 0 < m →
      LNChannels.RateBounds.biCost rate rate r B m m =
        2 * m + 2 * B * a ^ m / (a ^ m - 1) ^ 2 ∧
      ∀ C : ℝ, 0 < C →
        LNChannels.RateBounds.biCost rate rate r B m m - 2 * C * a / (a - 1) ^ 2 =
          2 * m + 2 * B * a ^ m / (a ^ m - 1) ^ 2 - 2 * C * a / (a - 1) ^ 2) := by sorry

end LightningChannels.SymmetricCosts
