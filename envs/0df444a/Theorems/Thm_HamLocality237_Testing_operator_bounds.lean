-- Prove2me | Theorems.Thm_HamLocality237_Testing_operator_bounds
-- name    : HamLocality237.Testing.operator_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:13.534999+00:00
-- url     : https://prove2.me/theorems/f8e90187-5116-4a31-a936-a36ffa664477
-- title:
--   §3.4 — bounded O and R and the inverse of D
-- statement:
--   The observation and response formulas define elements of $L^2(\mathbb R_+)$ and agree almost everywhere with the chosen bounded operators $O$ and $R$. Every finite-interval response integral is integrable, and
--
--   $$\|Ru\|_2\le\left(\int_0^\infty|\langle b,e^{-iM\tau}b\rangle|\,d\tau\right)\|u\|_2.$$
--
--   For every pair of nonnegative constants satisfying the two bounds of Lemma 3.3,
--
--   $$\|O\|^2\le C_{\rm obs},\qquad\|R\|\le C.$$
--
--   The kernel norm is integrable. Moreover $D=\eta^2I-R^\dagger R$ is self-adjoint, $D\succeq I$, its specified inverse is a two-sided bounded inverse, and $\|D^{-1}\|\le1$. Thus the definitions' choices use their intended branches.
--
--   Differences from the source:
--   - encoding: bounded maps defined by pointwise L2 formulas and the inverse D⁻¹ → a.e. formulas for Lp representatives, explicit membership/integrability, bounds for every valid pair of analytic constants, and both inverse identities; reason: L2 identifies representatives a.e.; the formulas certify the nonzero-choice branches, and the constants are precisely those supplied by Lemma 3.3
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §3.4, Eq. (17) and the paragraph defining D, p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Adversary

open MeasureTheory
open scoped BigOperators

namespace HamLocality237.Testing

theorem operator_bounds :
    (∀ r : BandSpace, MemLp (observationFormula r) 2 (volume.restrict (Set.Ici 0)) ∧
      observationOperator r =ᵐ[volume.restrict (Set.Ici 0)] observationFormula r) ∧
    (∀ u : HalfLineSpace, MemLp (responseFormula u) 2 (volume.restrict (Set.Ici 0)) ∧
      responseOperator u =ᵐ[volume.restrict (Set.Ici 0)] responseFormula u) ∧
    (∀ (u : HalfLineSpace) (t : ℝ), 0 ≤ t →
      IntervalIntegrable (fun s => observationFormula bumpVector (t - s) * u s) volume 0 t) ∧
    IntegrableOn (fun t => ‖observationFormula bumpVector t‖) (Set.Ici 0) ∧
    (∀ u : HalfLineSpace, ‖responseOperator u‖ ≤
      (∫ t in Set.Ici (0 : ℝ), ‖observationFormula bumpVector t‖) * ‖u‖) ∧
    (∀ C Cobs : ℝ, 0 ≤ C → 0 ≤ Cobs →
      (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal ‖observationFormula bumpVector t‖) ≤
        ENNReal.ofReal C →
      (∀ r : BandSpace,
        (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (‖observationFormula r t‖ ^ 2)) ≤
          ENNReal.ofReal (Cobs * ‖r‖ ^ 2)) →
      ‖observationOperator‖ ^ 2 ≤ Cobs ∧ ‖responseOperator‖ ≤ C) ∧
    penaltyInverse * penaltyOperator = 1 ∧ penaltyOperator * penaltyInverse = 1 ∧
    ‖penaltyInverse‖ ≤ 1 ∧ IsSelfAdjoint penaltyOperator ∧
    (∀ u : HalfLineSpace, ‖u‖ ^ 2 ≤ (inner ℂ u (penaltyOperator u)).re) := by sorry

end HamLocality237.Testing
