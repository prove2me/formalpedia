-- Prove2me | Theorems.Thm_GlobalTheory_AddCharProduct_finprod_psiE_eq_exp_trace
-- name    : GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:50.013387+00:00
-- url     : https://prove2.me/theorems/d9062b53-fbf6-49ce-8748-28afcf4331ff
-- title:
--   Add Char Product: finprod psi E eq exp trace
-- statement:
--   The Add Char Product construction uses the finprod psi E eq exp trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodPsiEEqExpTrace.lean#L21-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodPsiEEqExpTrace.lean#L21-L72

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinprodPsiEEqExpTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.AddCharProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p), ∀ x : E, (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧ ∏ᶠ p, (A p).psiE ((A p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by sorry
