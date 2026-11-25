-- Prove2me | Theorems.Thm_GlobalTheory_TUniq_emb_unique
-- name    : GlobalTheory.TUniq.emb_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:15.417308+00:00
-- url     : https://prove2.me/theorems/b5b7e664-0516-42d0-b1f1-b5c7cf62cfee
-- title:
--   TUniq: emb unique
-- statement:
--   The TUniq construction uses the emb unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L116-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L116-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem GlobalTheory.TUniq.emb_unique (hG : GlobalFnsSt) (t : TObj g (N' ^ 2) J b s) {m : ℕ} (hm : Odd m) {T : Over S}
    [Subsingleton T.left] {σ σ'} (H : t.Emb m T σ) (H' : t.Emb m T σ') {B : Type} [Field B]
    (y : Sp B ⟶ (T ⊗ t.A).left) {w} (h : SecCoord _ σ y w) : SecCoord _ σ' y w := by sorry
