-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_bijective_of_isIso_pullback
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_isIso_pullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:27:58.926821+00:00
-- url     : https://prove2.me/theorems/73850a2a-1a6f-4099-a77d-d0f4c02cb6cb
-- title:
--   Iso Thick: bijective of is Iso pullback
-- statement:
--   The Iso Thick construction uses the bijective of is Iso pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L108-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L108-L148

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick
open TensorProduct

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_isIso_pullback {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T] (φ : A →ₐ[R] B)
    (m : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (hm1 : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hm2 : m ≫ pullback.snd _ _ = pullback.snd _ _) (h : IsIso m) :
    Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R T)) := by sorry
