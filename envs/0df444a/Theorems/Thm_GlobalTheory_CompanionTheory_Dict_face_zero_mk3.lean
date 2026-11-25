-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dict_face_zero_mk3
-- name    : GlobalTheory.CompanionTheory.Dict.face_zero_mk3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:02.648838+00:00
-- url     : https://prove2.me/theorems/97be13e1-2d59-4f1f-9b8c-51cb70a5817b
-- title:
--   Dict: face zero mk3
-- statement:
--   The Dict construction uses the face zero mk3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L106-L107

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')

theorem GlobalTheory.CompanionTheory.Dict.face_zero_mk3 : face 0 (mk₃ φ ψ χ) = mk₂ ψ χ := by sorry
