-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_natCard_quotient_range_normUnits_eq_two
-- name    : GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:58.023531+00:00
-- url     : https://prove2.me/theorems/e75eeb0b-8253-4f37-b12f-ddccfa84f3af
-- title:
--   Automorphic: nat Card quotient range norm Units eq two
-- statement:
--   The Automorphic construction uses the nat Card quotient range norm Units eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L151-L154

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]

theorem GroundTheory.Automorphic.natCard_quotient_range_normUnits_eq_two :
    Nat.card (Fˣ ⧸ (normUnits F E).range) = 2 := by sorry
