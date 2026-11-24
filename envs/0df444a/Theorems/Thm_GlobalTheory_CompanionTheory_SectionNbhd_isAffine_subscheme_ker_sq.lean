-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SectionNbhd_isAffine_subscheme_ker_sq
-- name    : GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:38.503477+00:00
-- url     : https://prove2.me/theorems/66b8967e-b4bf-4a1c-81e1-60aac2455603
-- title:
--   Section Nbhd: is Affine subscheme ker sq
-- statement:
--   The Section Nbhd construction uses the is Affine subscheme ker sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodAffine.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquareZeroNeighbourhoodAffine.lean#L7-L49

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquareZeroNeighbourhoodAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SectionNbhd

theorem GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by sorry
