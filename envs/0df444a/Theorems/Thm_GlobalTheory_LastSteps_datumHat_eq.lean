-- Prove2me | Theorems.Thm_GlobalTheory_LastSteps_datumHat_eq
-- name    : GlobalTheory.LastSteps.datumHat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:46.470504+00:00
-- url     : https://prove2.me/theorems/795e9839-f263-4b20-bd52-39816dc1634d
-- title:
--   Last Steps: datum Hat eq
-- statement:
--   The Last Steps construction uses the datum Hat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L330-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactQLat.lean#L330-L370

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
variable [Fintype n]
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
variable [Fintype n'] (ε : 𝒪[k]ˣ) (P : Pair k n') (x₀ : Matrix n n' k) (η : n → k)

theorem GlobalTheory.LastSteps.datumHat_eq :
    Integrable (fun y => datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ)) μ ∧
      datumHat ψ ε μ q P L x₀ η = (volQ μ q L : ℂ) * ∑ᶠ fW : Module.Dual 𝓀[k] (Red L),
        term q (resChar ψ hψ q) (resUnit ε) P L fW x₀ * cosetInd q L fW η := by sorry
