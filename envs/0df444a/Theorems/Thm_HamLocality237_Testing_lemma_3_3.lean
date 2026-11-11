-- Prove2me | Theorems.Thm_HamLocality237_Testing_lemma_3_3
-- name    : HamLocality237.Testing.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:59.895754+00:00
-- url     : https://prove2.me/theorems/12f77965-12a3-49fe-8a79-27284f5d7bf0
-- title:
--   Lemma 3.3 — both uniform half-line analytic bounds
-- statement:
--   For the fixed normalized bump $b$ and multiplication operator $M$, there are finite nonnegative real constants $C,C_{\rm obs}$ such that
--
--   $$\int_0^\infty|\langle b,e^{-iM\tau}b\rangle|\,d\tau\le C,\qquad
--   \int_0^\infty|\langle b,e^{-iM\tau}r\rangle|^2\,d\tau\le C_{\rm obs}\|r\|^2$$
--
--   for every $r\in L^2([-1/2,1/2])$. Both constants precede the arbitrary vector and are independent of the algorithm, precision and elapsed time. These are the two analytic properties specific to the continuous hard distribution.
--
--   Differences from the source:
--   - encoding: finite integrals of absolute values and absolute squares → nonnegative Lebesgue integrals bounded by finite ENNReal images of real constants; reason: an infinite or nonintegrable nonnegative integrand cannot satisfy the bound; the nonnegative constants can always be chosen for the source bounds
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Lemma 3.3, pp.14–15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem lemma_3_3 :
    ∃ C Cobs : ℝ, 0 ≤ C ∧ 0 ≤ Cobs ∧
      (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal ‖observationFormula bumpVector t‖) ≤
        ENNReal.ofReal C ∧
      ∀ r : BandSpace,
        (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (‖observationFormula r t‖ ^ 2)) ≤
          ENNReal.ofReal (Cobs * ‖r‖ ^ 2) := by sorry

end HamLocality237.Testing
