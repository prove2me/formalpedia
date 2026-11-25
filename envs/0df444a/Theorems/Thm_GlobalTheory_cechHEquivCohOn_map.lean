-- Prove2me | Theorems.Thm_GlobalTheory_cechHEquivCohOn_map
-- name    : GlobalTheory.cechHEquivCohOn_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:45.758278+00:00
-- url     : https://prove2.me/theorems/6aa6db44-1655-5eab-8add-bfbc5931d7e9
-- title:
--   Global Theory: cech HEquiv Coh On map
-- statement:
--   The Global Theory construction uses the cech HEquiv Coh On map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L386-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L386-L390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)

theorem GlobalTheory.cechHEquivCohOn_map (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod V U G)
    (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHEquivCohOn R hc hG n ((cechHMap R V U φ n).hom x) =
      cohOn.map R φ V n (cechHEquivCohOn R hc hF n x) := by sorry
