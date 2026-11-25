-- Prove2me | Theorems.Thm_GlobalTheory_Spread_comp_eq_id_of_models
-- name    : GlobalTheory.Spread.comp_eq_id_of_models
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:05.198781+00:00
-- url     : https://prove2.me/theorems/89571d3b-e7fd-4d48-a2b3-f93bcfa1baec
-- title:
--   Spread: comp eq id of models
-- statement:
--   The Spread construction uses the comp eq id of models property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothModelsIsoOverFgSubalgebra.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothModelsIsoOverFgSubalgebra.lean#L26-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothModelsIsoOverFgSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.Spread
variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem GlobalTheory.Spread.comp_eq_id_of_models [Flat p] [IsSeparated p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) (R : Subalgebra k V)
    (f : pullback p (spMap (algebraMap k R)) ⟶ pullback q (spMap (algebraMap k R)))
    (g : pullback q (spMap (algebraMap k R)) ⟶ pullback p (spMap (algebraMap k R)))
    (hf : f ≫ pullback.snd _ _ = pullback.snd _ _) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ')
    (hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ) :
    f ≫ g = 𝟙 _ := by sorry
