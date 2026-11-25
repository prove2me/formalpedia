-- Prove2me | Theorems.Thm_GlobalTheory_ResProd_prod_resQ_zpow
-- name    : GlobalTheory.ResProd.prod_resQ_zpow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:15.643202+00:00
-- url     : https://prove2.me/theorems/64c73b6a-1f87-4385-8c19-1e846dae1918
-- title:
--   Res Prod: prod res Q zpow
-- statement:
--   The Res Prod construction uses the prod res Q zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ProdResQZpow.lean#L75-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ProdResQZpow.lean#L75-L105

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProdResQZpow
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
open GlobalTheory GlobalTheory.ResProd

theorem GlobalTheory.ResProd.prod_resQ_zpow : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → ∀ x : F, x ≠ 0 → {p | vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) ≠ 0}.Finite ∧ ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF x)) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by sorry
