-- Prove2me | Theorems.Thm_GoodViewsNotEnough_global_regularizer_separation
-- name    : GoodViewsNotEnough.global_regularizer_separation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:49:55.224971+00:00
-- url     : https://prove2.me/theorems/93d60539-4f7b-4148-a44f-5ce0e4c9ea5f
-- title:
--   Lemma 3: global regularizer separation
-- statement:
--   Let $D$ be either the analytic discrepancy $D_{\rm an}$ (frequency measure $e^{-t^2/2}dt$) or the grid discrepancy $D_{\rm gr}$ (17 nodes $t_j=5j/8$). Then:
--
--   1. every equally weighted two-atom law satisfies $D\big(\tfrac12(\delta_b+\delta_c)\big)>\tfrac1{50}$ for all $b,c\in\mathbb{R}$;
--   2. the comparator $w=(1/10,13/10,-1/10,-13/10)$ satisfies $P_\pi(w)=\tfrac{121}{400}$ and $D(\mu_w)<\tfrac3{1000}$;
--   3. the frequency mass satisfies $A_\nu<\tfrac{251}{100}$;
--   4. the minimum of $D_{\rm an}$ over two-atom laws is attained and equals
--
--   $$d_*=\frac{\sqrt{2\pi}}2+\sqrt{\frac{2\pi}3}-\frac74\sqrt\pi\,2^{-3/14}>\frac{357}{16000}>\frac1{50}.$$
--
--   A scene-only scalar encoder has a two-atom output law, so this lemma bounds the Gaussian discrepancy from below on the entire scene-only class.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix B.2, Lemma 3, eqs. (10)-(12), p. 12

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem global_regularizer_separation :
    (∀ ν ∈ ({analyticFreq, gridFreq} : Set (Measure ℝ)),
      (∀ b c : ℝ, 1 / 50 < discrepancy ν (twoAtomLaw b c)) ∧
      discrepancy ν (scalarLaw scalarComparator) < 3 / 1000 ∧
      freqMass ν < 251 / 100) ∧
    scalarPred scalarPairLaw scalarComparator = 121 / 400 ∧
    IsLeast (Set.range fun bc : ℝ × ℝ => discrepancy analyticFreq (twoAtomLaw bc.1 bc.2))
      analyticTwoAtomMin ∧
    357 / 16000 < analyticTwoAtomMin ∧ (1 / 50 : ℝ) < 357 / 16000 := by sorry

end GoodViewsNotEnough
