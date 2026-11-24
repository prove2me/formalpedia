-- Prove2me | Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_twist_iff
-- name    : GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:52:58.636798+00:00
-- url     : https://prove2.me/theorems/5a27ea0f-ab5d-44cb-a8b3-42a84d72a7a4
-- title:
--   Jacquet Blocks: has Finite Length twist iff
-- statement:
--   The Jacquet Blocks construction uses the has Finite Length twist iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean#L16-L33

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
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
open GlobalTheory GlobalTheory.JacquetBlocks
variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by sorry
