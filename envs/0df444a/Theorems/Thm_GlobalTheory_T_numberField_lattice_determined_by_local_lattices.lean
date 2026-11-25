-- Prove2me | Theorems.Thm_GlobalTheory_T_numberField_lattice_determined_by_local_lattices
-- name    : GlobalTheory.T.numberField_lattice_determined_by_local_lattices
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:28.298924+00:00
-- url     : https://prove2.me/theorems/7c6e5d96-ff11-5f52-8183-1896a04c0c37
-- title:
--   T: number Field lattice determined by local lattices
-- statement:
--   The T construction uses the number Field lattice determined by local lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NumberFieldLatticeDeterminedByLocalLatticesStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NumberFieldLatticeDeterminedByLocalLatticesStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLattices
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
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

theorem GlobalTheory.T.numberField_lattice_determined_by_local_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧ {p | A.lat p Λ ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by sorry
