-- Prove2me | Theorems.Thm_GlobalTheory_PrescribedRank_constMap_injective
-- name    : GlobalTheory.PrescribedRank.constMap_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:50.359834+00:00
-- url     : https://prove2.me/theorems/246a9177-6980-47a8-bef5-09304104d841
-- title:
--   Prescribed Rank: const Map injective
-- statement:
--   The Prescribed Rank construction uses the const Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L93-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ConstMapInjective.lean#L93-L104

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

theorem GlobalTheory.PrescribedRank.constMap_injective (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by sorry
