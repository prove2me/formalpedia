-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatExt_rational_extend
-- name    : GlobalTheory.HL.RatExt.rational_extend
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:36:28.329723+00:00
-- url     : https://prove2.me/theorems/e95930db-4820-511e-9588-ded37e73decf
-- title:
--   Rat Ext: rational extend
-- statement:
--   The Rat Ext construction uses the rational extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L80-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RationalExtend.lean#L80-L150

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatExt
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.RatExt.rational_extend : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (n : ℕ) (p : HeightOneSpectrum (𝓞 F)), Function.Injective (A.bc (n := n) p) ∧ Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ ∧ (∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃! g', A.Ext p g g') ∧ (∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) g' (Λ : Submodule (𝓞 E) (Fin n → E)), A.Ext p g g' → A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ) ∧ (∀ (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E), _root_.GlobalTheory.HL.hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * Hm i j * sig (y j))) ∧ ∀ (m : ℕ) (v : Fin m → Fin n → E), LinearIndependent E v ↔ LinearIndependent (A.loc p).Ep fun a => A.bc p (v a) := by sorry
