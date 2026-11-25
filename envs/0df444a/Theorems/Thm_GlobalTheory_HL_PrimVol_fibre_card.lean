-- Prove2me | Theorems.Thm_GlobalTheory_HL_PrimVol_fibre_card
-- name    : GlobalTheory.HL.PrimVol.fibre_card
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:05:57.336802+00:00
-- url     : https://prove2.me/theorems/69c1155f-2cd6-47af-af10-a7ef59a46772
-- title:
--   Prim Vol: fibre card
-- statement:
--   The Prim Vol construction uses the fibre card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L224-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L224-L312

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
import Theorems.Thm_GlobalTheory_GramCount_Prim_map

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem GlobalTheory.HL.PrimVol.fibre_card {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hcj : ∀ x ∈ L.O, L.cj x ∈ L.O)
    {p : E} (hp : p ∈ L.O) (hp' : IsUnit p) (hc : L.cj p = p)
    (hu : ∀ c ∈ L.O, ∃ u ∈ L.O, (1 + p * c) * u = 1)
    (b : Fin n → Fin n → E) (hb : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (hbΛ : Λ = Submodule.span L.O (Set.range b)) (R : Finset E) (hR : ∀ u ∈ R, u ∈ L.O)
    (hR' : ∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = p * c)
    {G : Matrix (Fin m) (Fin m) E} (hG : IsHerm L G) (S : Set (Fin m → Fin n → E))
    (hS : S = {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧
      (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧
        ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧
      ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - G a b = p * c})
    (U : Set ((Fin m → Fin n → E) ⧸ (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ p)))
    (hU : U = QuotientAddGroup.mk '' {z | IsPrimT L Hm Λ z ∧
      gramT L Hm z - G ∈ (hermLat L m).map (DistribMulAction.toAddMonoidHom _ p)}) :
    U.Finite ∧ U.ncard = S.ncard := by sorry
