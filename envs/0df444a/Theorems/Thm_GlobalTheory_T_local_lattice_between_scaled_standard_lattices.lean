-- Prove2me | Theorems.Thm_GlobalTheory_T_local_lattice_between_scaled_standard_lattices
-- name    : GlobalTheory.T.local_lattice_between_scaled_standard_lattices
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:18.126952+00:00
-- url     : https://prove2.me/theorems/ccce744e-b82d-4809-b82b-050f1d2d0842
-- title:
--   T: local lattice between scaled standard lattices
-- statement:
--   The T construction uses the local lattice between scaled standard lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLatticesStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalLatticeBetweenScaledStandardLatticesStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLattices
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeBetweenScaledStandardLatticesStatement
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

theorem GlobalTheory.T.local_lattice_between_scaled_standard_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)), IsLat (A.L p) Λ → (∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) → ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧ ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O := by sorry
