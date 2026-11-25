-- Prove2me | Theorems.Thm_GlobalTheory_HL_Glue_exists_nat_smul_mem
-- name    : GlobalTheory.HL.Glue.exists_nat_smul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:33:27.62526+00:00
-- url     : https://prove2.me/theorems/1e3aaa79-2fc7-405c-b75c-c85731d969ec
-- title:
--   Glue: exists nat smul mem
-- statement:
--   The Glue construction uses the exists nat smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLattices.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLattices.lean#L23-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Theorems.Thm_GlobalTheory_NatSmulMem_exists_nat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem GlobalTheory.HL.Glue.exists_nat_smul_mem (Λ : Submodule O (Fin n → R))
    (hd : ∀ y : R, ∃ m : ℕ, m ≠ 0 ∧ (m : R) * y ∈ O) {x : Fin n → R}
    (hx : x ∈ Submodule.span R (Λ : Set (Fin n → R))) : ∃ m : ℕ, m ≠ 0 ∧ (m : R) • x ∈ Λ := by sorry
