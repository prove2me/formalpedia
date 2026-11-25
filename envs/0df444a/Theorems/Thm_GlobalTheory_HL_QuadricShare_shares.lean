-- Prove2me | Theorems.Thm_GlobalTheory_HL_QuadricShare_shares
-- name    : GlobalTheory.HL.QuadricShare.shares
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:16.780076+00:00
-- url     : https://prove2.me/theorems/7f7bfc42-9410-501e-bdbe-76db7cc37f54
-- title:
--   Quadric Share: shares
-- statement:
--   The Quadric Share construction uses the shares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/QuadricCharacterLeakSharesFinite.lean#L285-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/QuadricCharacterLeakSharesFinite.lean#L285-L372

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsTraceChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TwoGeometricSumsIndexBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuadricShare
open GlobalTheory.HL.GaussSummand
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HL.QuadricShare.shares : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by sorry
