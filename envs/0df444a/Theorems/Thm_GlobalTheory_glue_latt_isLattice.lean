-- Prove2me | Theorems.Thm_GlobalTheory_glue_latt_isLattice
-- name    : GlobalTheory.glue_latt_isLattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:51.45753+00:00
-- url     : https://prove2.me/theorems/66c8c8a5-e769-5370-a8fc-e89560d6a74e
-- title:
--   Global Theory: glue latt is Lattice
-- statement:
--   The Global Theory construction uses the glue latt is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeOfSqueezedBetweenNatMultiples.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeOfSqueezedBetweenNatMultiples.lean#L11-L39

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiples
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

theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by sorry
