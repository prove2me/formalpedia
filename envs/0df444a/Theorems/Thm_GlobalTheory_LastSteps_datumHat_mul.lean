-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_datumHat_mul
-- name    : GlobalTheory.LastSteps.datumHat_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:36.674795+00:00
-- url     : https://prove2.me/theorems/05587b31-bfbb-4c80-a853-b00d73f7057d
-- title:
--   Last Steps: datum Hat mul
-- statement:
--   The Last Steps construction uses the datum Hat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L470-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L470-L484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure]

theorem GlobalTheory.LastSteps.datumHat_mul (P : Pair k n') :
    latInd LY L'' x' • (fun x₀ => datumHat ψ ε μ q P LY x₀ η) = (volQ μ q LY : ℂ) •
      ((latInd LY L'' x' * cosetInd q LY 0 η) • latInd P.ker LY +
        ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
          (latInd P.ker Q.ker + mainDatum q (resChar ψ hψ q) (resUnit ε) P Q)) := by sorry
