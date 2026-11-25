-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_norm_add_norm_ne
-- name    : GroundTheory.Automorphic.exists_norm_add_norm_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:01.650875+00:00
-- url     : https://prove2.me/theorems/0474d5be-29e4-5097-a3a2-c2da05696a38
-- title:
--   Automorphic: exists norm add norm ne
-- statement:
--   The Automorphic construction uses the exists norm add norm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L47-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L47-L117

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

theorem GroundTheory.Automorphic.exists_norm_add_norm_ne (hN : Nat.card (Fˣ ⧸ (normUnits F E).range) = 2)
    (hsq : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F)) :
    ∃ x y : E, ∀ z : E, Algebra.norm F x + Algebra.norm F y ≠ Algebra.norm F z := by sorry
