-- Prove2me | Theorems.Thm_GlobalTheory_AddCharProduct_main_prime_pow
-- name    : GlobalTheory.AddCharProduct.main_prime_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:48:08.581802+00:00
-- url     : https://prove2.me/theorems/6e2f2033-25a9-50ee-8311-2476034b7869
-- title:
--   Add Char Product: main prime pow
-- statement:
--   The Add Char Product construction uses the main prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodPsiEEqExpTrace.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FinprodPsiEEqExpTrace.lean#L13-L19

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

theorem GlobalTheory.AddCharProduct.main_prime_pow (h2 : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    (Function.mulSupport fun p => (A p).psiE ((A p).ιE (y / (l : E) ^ k))).Finite ∧
      ∏ᶠ p, (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ))) := by sorry
