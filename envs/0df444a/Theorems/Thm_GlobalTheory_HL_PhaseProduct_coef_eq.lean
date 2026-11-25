-- Prove2me | Theorems.Thm_GlobalTheory_HL_PhaseProduct_coef_eq
-- name    : GlobalTheory.HL.PhaseProduct.coef_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:18.452215+00:00
-- url     : https://prove2.me/theorems/f9cbf934-6572-4902-9bca-6651f9a88d3b
-- title:
--   Phase Product: coef eq
-- statement:
--   The Phase Product construction uses the coef eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PsiOfEq.lean#L18-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PsiOfEq.lean#L18-L49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinprodPsiEEqExpTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PsiOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PhaseProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem GlobalTheory.HL.PhaseProduct.coef_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) (a : Fin r) :
    (G.S p).coef sf se m a = algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) *
      (A.loc p).ιE (∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) := by sorry
