-- Prove2me | Theorems.Thm_GlobalTheory_HL_EichCont_prod_eich_cont
-- name    : GlobalTheory.HL.EichCont.prod_eich_cont
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:18.203022+00:00
-- url     : https://prove2.me/theorems/dca34e43-a6e6-5d72-90a1-319c027adafd
-- title:
--   Eich Cont: prod eich cont
-- statement:
--   The Eich Cont construction uses the prod eich cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianEichlerProductContinuousOnLattice.lean#L355-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianEichlerProductContinuousOnLattice.lean#L355-L533

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLattice
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichCont
open ValuativeRel NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.EichCont.prod_eich_cont : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E)
    (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (he : ∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v)
    (Λ : Submodule L.O (Fin N → E)) (hΛ : _root_.GlobalTheory.HL.IsLat L Λ) (c : Fˣ),
    ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E)
      (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)),
      (∀ i v, e' i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u' i) (s' i) v) →
      (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) →
      (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) →
      ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x =
        algebraMap F E c • y := by sorry
