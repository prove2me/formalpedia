-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_relIndex_prod_prod
-- name    : GlobalTheory.BorelUMod.relIndex_prod_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:03:21.689067+00:00
-- url     : https://prove2.me/theorems/aed21f24-89f5-410f-945f-c4c3ebc2eb97
-- title:
--   Borel UMod: rel Index prod prod
-- statement:
--   The Borel UMod construction uses the rel Index prod prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_IsOpposite_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod

theorem GlobalTheory.BorelUMod.relIndex_prod_prod {G G' : Type} [AddGroup G] [AddGroup G'] (H K : AddSubgroup G) (H' K' : AddSubgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by sorry
