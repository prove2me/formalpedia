-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L2_dn_one_eq_d1_L1
-- name    : GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:57:53.831238+00:00
-- url     : https://prove2.me/theorems/15eeb768-6d2a-527a-b4f9-0b8982f9c3de
-- title:
--   Dict: L2 dn one eq d1 L1
-- statement:
--   The Dict construction uses the L2 dn one eq d1 L1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L130-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean#L130-L139

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

theorem GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1 (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by sorry
