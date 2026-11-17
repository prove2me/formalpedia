-- Prove2me | Theorems.Thm_Kyprianou_Ch07_upwardCreepingLevyTripletCriterion
-- name    : Kyprianou.Ch07.upwardCreepingLevyTripletCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:52:39.272192+00:00
-- url     : https://prove2.me/theorems/47cb7a5c-0315-4679-8c52-f417ee7ff7f6
-- title:
--   Theorem 7.11: complete three-case criterion for upward creeping
-- statement:
--   For every non-compound-Poisson real Lévy process with the actual Lévy–Khintchine triplet (b,σ²,Π), upward creeping has positive probability if and only if (i) its paths are of bounded variation with canonical finite-variation drift d=b−∫_{|x|<1}xΠ(dx)>0; or (ii) its Gaussian coefficient is positive; or (iii) it has unbounded variation, no Gaussian component, and the exact small-positive-jump to integrated negative-tail test ∫₀¹ xΠ(x,∞)/(∫₀ˣΠ(−1,−u)du)dx is finite. No condition is assumed from the conclusion.
-- source:
--   Kyprianou (2006), Theorem 7.11(i)–(iii), printed pp.198–199, original PDF physical pp.207–208, Windows Ky.pdf sheets 104–105.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.11, complete three-case upward creeping criterion. -/
theorem upwardCreepingLevyTripletCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi) :
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let unboundedPureJump : Prop :=
      sigma2 = 0 ∧ ¬ finiteVariationJumpMass
    let mixedJumpCriterion : Prop :=
      (∫⁻ x : Real in Set.Ioo 0 1,
         (ENNReal.ofReal x * Pi (Set.Ioi x)) /
         (∫⁻ u : Real in Set.Ioo 0 x,
            Pi (Set.Ioo (-1) (-u)) ∂volume) ∂volume) < ⊤
    (0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1 ↔
      ((sigma2 = 0 ∧ finiteVariationJumpMass ∧ 0 < canonicalDrift) ∨
       (0 < sigma2) ∨
       (unboundedPureJump ∧ mixedJumpCriterion))) := by
  sorry

end Kyprianou.Ch07
