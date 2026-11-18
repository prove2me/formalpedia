-- Prove2me | Theorems.Thm_OWMR_dfr_mirror_bound
-- name    : OWMR.dfr_mirror_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:13.293798+00:00
-- url     : https://prove2.me/theorems/35221b9a-79e2-4610-b681-1bb4ee259ae0
-- title:
--   Lemma D.2 (nonincreasing-density mirror bound): $B_{S-s}\le p\bigl(1-\sqrt{p/(p+h)}\bigr)(S-s)$ when $x\mapsto U[0,x]$ is concave
-- statement:
--   Let $\rho$ be a probability law on $[0,\infty)$ with positive mean and renewal measure $U$, let $h,p>0$ and $s<S$, and suppose $x\mapsto U[0,x]$ is concave on $[0,S-s]$. Let $\mathrm{mirrorAvg}(s,S,a)$ be the long-run average of $\phi(a-\widehat P_t)$ over the post-order positions $\widehat P_t$ of the $(s,S)$ policy, with $\phi(y)=hy^++py^-$, and let $\mathrm{mirrorCost}(s,S)=\inf_a\mathrm{mirrorAvg}(s,S,a)$ be its mirror cost (14). Then
--   $$\mathrm{mirrorCost}(s,S)\le p\Bigl(1-\sqrt{\tfrac{p}{p+h}}\Bigr)(S-s).$$
--   Concavity of $x\mapsto U[0,x]$ means that the long-run depletion $S-\widehat P$ has an atom at zero and a nonincreasing density on $(0,S-s)$, the hypothesis of Lemma D.2.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, Lemma D.2 (Nonincreasing-Density Mirror Bound) and (D.4), p. E.25, proved in Appendix D.1, p. E.28; mirror cost $B_w$ in (14).

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem dfr_mirror_bound (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p s S : ℝ) (hh : 0 < h) (hp : 0 < p) (hsS : s < S)
    (hconc : ConcaveOn ℝ (Set.Icc 0 (S - s))
      (fun x => (renewalMeasure ρ (Set.Icc 0 x)).toReal)) :
    mirrorCost ρ h p s S ≤ ENNReal.ofReal (p * (1 - Real.sqrt (p / (p + h))) * (S - s)) := by sorry
end OWMR
