-- Prove2me | Theorems.Thm_GlobalTheory_HL_PhaseProduct_psiOf_eq
-- name    : GlobalTheory.HL.PhaseProduct.psiOf_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:20.584998+00:00
-- url     : https://prove2.me/theorems/6e312ac5-cbae-42cd-9e9f-9394dba5ffda
-- title:
--   Phase Product: psi Of eq
-- statement:
--   The Phase Product construction uses the psi Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PsiOfEq.lean#L51-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PsiOfEq.lean#L51-L89

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

theorem GlobalTheory.HL.PhaseProduct.psiOf_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (δ : ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹)))
    (h2 : (G.c p : (A.loc p).Fp) * g = δ * (G.S p).th)
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) :
    (G.S p).psiOf sf se m = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) / g))) := by sorry
