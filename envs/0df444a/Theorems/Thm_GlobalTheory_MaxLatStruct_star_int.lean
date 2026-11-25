-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_star_int
-- name    : GlobalTheory.MaxLatStruct.star_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:00:49.479267+00:00
-- url     : https://prove2.me/theorems/00d12ca0-c2fa-46bb-b339-dc91ba3937a5
-- title:
--   Max Lat Struct: star int
-- statement:
--   The Max Lat Struct construction uses the star int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L475-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L475-L477

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct

theorem GlobalTheory.MaxLatStruct.star_int {K : Type} [Field K] [NumberField K] [StarRing K] :
    ∃ σ : 𝓞 K →+* 𝓞 K, ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r) := by sorry
