-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_algebraMap_quadratic
-- name    : GroundTheory.Automorphic.norm_algebraMap_quadratic
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:07.457886+00:00
-- url     : https://prove2.me/theorems/96751d6d-8f69-43b5-a9a6-03632ab64118
-- title:
--   Automorphic: norm algebra Map quadratic
-- statement:
--   The Automorphic construction uses the norm algebra Map quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L30-L31

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
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

theorem GroundTheory.Automorphic.norm_algebraMap_quadratic (t : F) : Algebra.norm F (algebraMap F E t) = t ^ 2 := by sorry
