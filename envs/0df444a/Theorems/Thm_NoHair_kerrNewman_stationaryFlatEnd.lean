-- Prove2me | Theorems.Thm_NoHair_kerrNewman_stationaryFlatEnd
-- name    : NoHair.kerrNewman_stationaryFlatEnd
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:16.530873+00:00
-- url     : https://prove2.me/theorems/478ab9ca-43c9-4348-9e9f-67d6d2445b81
-- title:
--   Kerr–Schild time translations and the standard stationary asymptotically flat end
-- statement:
--   For $m>0$ and $a^2+e^2\le m^2$, write $r_+=m+\sqrt{m^2-a^2-e^2}$ and let $\rho=\sqrt{x^2+y^2+z^2}$ be the Euclidean spatial radius. On the Kerr–Newman manifold $\{r>0\}$, time translation $\varphi_s(t,\mathbf{x})=(t+s,\mathbf{x})$ is a smooth symmetry of both the metric and the Maxwell field. There is a stationary asymptotically flat end $E$ with
--
--   $$E_{\rm region}=\{\rho>R\},\qquad R>r_++|a|.$$
--
--   In its adapted coordinates the metric perturbation is $O(\rho^{-1})$, and its first derivatives and the field components are $O(\rho^{-2})$. The explicit end region allows its causal past and future to be computed in the same coordinates.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, https://arxiv.org/abs/1410.6626v2, §3.1, Boyer–Lindquist asymptotics and Cartesian Kerr–Schild Eqs. (3.15)–(3.16); Prove2Me, NoHair.kerrNewman_isStationaryBlackHole, https://prove2.me/theorems/d4aa60f2-99c7-4a52-9c28-6ba24b2ddbac, stationary asymptotically flat end.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.kerrNewman_stationaryFlatEnd (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ),
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ ∧
      kerrNewmanOuterRadius m a e + |a| < E.R ∧
      E.region = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion E.R := by sorry
