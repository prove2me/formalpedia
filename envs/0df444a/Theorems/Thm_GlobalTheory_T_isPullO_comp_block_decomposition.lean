-- Prove2me | Theorems.Thm_GlobalTheory_T_isPullO_comp_block_decomposition
-- name    : GlobalTheory.T.isPullO_comp_block_decomposition
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:53.011309+00:00
-- url     : https://prove2.me/theorems/3981f8fc-2458-491d-9280-d8bee8c922d9
-- title:
--   T: is Pull O comp block decomposition
-- statement:
--   The T construction uses the is Pull O comp block decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsPullOWOverCompStatement.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsPullOWOverCompStatement.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverComp
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isPullO_comp_block_decomposition : ∀ (R : Type) [CommRing R] (X Y Z : Over (Sp R)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom), IsPullO (wOver g) a b → IsPullO (wOver f) b c →
    IsPullO (wOver (f ≫ g)) a c := by sorry
