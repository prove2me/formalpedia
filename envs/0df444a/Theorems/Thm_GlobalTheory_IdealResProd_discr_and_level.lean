-- Prove2me | Theorems.Thm_GlobalTheory_IdealResProd_discr_and_level
-- name    : GlobalTheory.IdealResProd.discr_and_level
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:48.375703+00:00
-- url     : https://prove2.me/theorems/c0a936a4-f579-430f-a627-fb2ca50e9e49
-- title:
--   Ideal Res Prod: discr and level
-- statement:
--   The Ideal Res Prod construction uses the discr and level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L134-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AbsNormEqFinprod.lean#L134-L172

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsNormEqFinprod
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
open GlobalTheory GlobalTheory.IdealResProd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}

theorem GlobalTheory.IdealResProd.discr_and_level : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → (∀ c : ∀ p, ((A.loc p).Fp)ˣ, (∀ p, Submodule.span (A.L p).O ((fun x : 𝓞 F => (A.loc p).ιE (algebraMap F E x)) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) = Submodule.span (A.L p).O {algebraMap (A.loc p).Fp (A.loc p).Ep (c p)}) → ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep (c p)) = |(NumberField.discr F : ℝ)|) ∧ ∀ g : ℕ, g ≠ 0 → (∀ p : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ p.asIdeal → ∃ u : (𝒪[(A.loc p).Fp])ˣ, (g : (A.loc p).Fp) = ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) * (ϖ p : (A.loc p).Fp)) → ∏ᶠ p : HeightOneSpectrum (𝓞 F), (if (g : 𝓞 F) ∈ p.asIdeal then (resQ (ϖ p) : ℝ) else 1) = (g : ℝ) ^ Module.finrank ℚ F := by sorry
