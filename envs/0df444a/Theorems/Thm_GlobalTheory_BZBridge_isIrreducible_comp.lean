-- Prove2me | Theorems.Thm_GlobalTheory_BZBridge_isIrreducible_comp
-- name    : GlobalTheory.BZBridge.isIrreducible_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:01.597827+00:00
-- url     : https://prove2.me/theorems/07068b62-a586-4a91-a922-c469242a6fb0
-- title:
--   BZBridge: is Irreducible comp
-- statement:
--   The BZBridge construction uses the is Irreducible comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L29-L32

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleAdmissible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BZBridge
variable {H G V : Type} [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.BZBridge.isIrreducible_comp (π : Representation ℂ G V) (Φ : H ≃* G) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp Φ.toMonoidHom : Representation ℂ H V) := by sorry
