-- Prove2me | Theorems.Thm_GlobalTheory_BZBridge_isSmooth_comp
-- name    : GlobalTheory.BZBridge.isSmooth_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:56.269797+00:00
-- url     : https://prove2.me/theorems/a109406a-0c92-4e32-966b-a96e1c777b7c
-- title:
--   BZBridge: is Smooth comp
-- statement:
--   The BZBridge construction uses the is Smooth comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleAdmissible.lean#L34-L37

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleAdmissible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp

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

theorem GlobalTheory.BZBridge.isSmooth_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (h : IsSmooth π) :
    IsSmooth (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V) := by sorry
