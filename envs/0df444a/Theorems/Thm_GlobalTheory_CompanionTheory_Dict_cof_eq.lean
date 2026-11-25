-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cof_eq
-- name    : GlobalTheory.CompanionTheory.Dict.cof_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:30:35.541613+00:00
-- url     : https://prove2.me/theorems/c96bfe86-7b71-46d5-9d32-03a4ac6df6cc
-- title:
--   Dict: cof eq
-- statement:
--   The Dict construction uses the cof eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L62-L68

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

theorem GlobalTheory.CompanionTheory.Dict.cof_eq {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ C) (c' : Fin (n + 1) ⥤ C)
    (h : face i c = c') (u : c'.obj (Fin.last n) ⟶ c.obj (Fin.last (n + 1)))
    (hu : HEq (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) u) (f : Cn F n) :
    cof F n i f c = mp F u (f c') := by sorry
