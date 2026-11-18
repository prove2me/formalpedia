-- Prove2me | Theorems.Thm_OWMR_renewal_concave_dfr
-- name    : OWMR.renewal_concave_dfr
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:12.454046+00:00
-- url     : https://prove2.me/theorems/8e1ff2b1-84ca-487a-add8-70203dd24eda
-- title:
--   Brown's concavity theorem: with log-convex survival, $x\mapsto U[0,x]$ is concave on $[0,\infty)$
-- statement:
--   Let $\rho$ be a probability law on $[0,\infty)$ with positive mean, and let $\bar G(x)=\rho(x,\infty)$ be its survival function. Suppose $\bar G$ is log-convex on $[0,\infty)$: for $x,y\ge0$ and $0\le\eta\le1$,
--   $$\bar G(\eta x+(1-\eta)y)\le\bar G(x)^{\eta}\,\bar G(y)^{1-\eta}.$$
--   Let $U=\sum_{k\ge0}\rho^{*k}$ be the renewal measure, including the initial renewal at zero (`renewalMeasure`). Then the renewal function $x\mapsto U[0,x]$ is concave on $[0,\infty)$.
--
--   The law may have an atom at zero. Dividing $\bar G$ by $\bar G(0)=\mathbb P(D>0)$ shows that the hypothesis is exactly log-convexity of the survival function conditional on positive demand, the DFR property of Appendix D.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, paragraph before the proof of Theorem D.1, p. E.25: for absolutely continuous DFR $D^+$, $x\mapsto U_+[0,x]$ is concave on $[0,\infty)$ (Brown 1980; Yu 2011), and $U=q^{-1}U_+$ with $q=\mathbb P(D>0)$.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewal_concave_dfr (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      (ρ {z : ℝ≥0 | η * x + (1 - η) * y < (z : ℝ)}).toReal
        ≤ (ρ {z : ℝ≥0 | x < (z : ℝ)}).toReal ^ η * (ρ {z : ℝ≥0 | y < (z : ℝ)}).toReal ^ (1 - η)) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (renewalMeasure ρ (Set.Icc 0 x)).toReal) := by sorry
end OWMR
