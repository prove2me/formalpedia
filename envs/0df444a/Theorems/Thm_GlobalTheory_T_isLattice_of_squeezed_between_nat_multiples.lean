-- Prove2me | Theorems.Thm_GlobalTheory_T_isLattice_of_squeezed_between_nat_multiples
-- name    : GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:07.215273+00:00
-- url     : https://prove2.me/theorems/1ce87fbe-a486-5869-abe9-127991bad0f4
-- title:
--   T: is Lattice of squeezed between nat multiples
-- statement:
--   The T construction uses the is Lattice of squeezed between nat multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeOfSqueezedBetweenNatMultiplesStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsLatticeOfSqueezedBetweenNatMultiplesStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiples
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiplesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples : ∀ {E : Type} [Field E] [NumberField E], ∀ (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → (∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ) → (∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) → Submodule.IsLattice E Γ := by sorry
