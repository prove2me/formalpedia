-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tensor_ext
-- name    : GlobalTheory.CompanionTheory.CotLoc.tensor_ext
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:03.319805+00:00
-- url     : https://prove2.me/theorems/c460d1db-8fe8-4eec-affa-0fd1949be9ef
-- title:
--   Cot Loc: tensor ext
-- statement:
--   The Cot Loc construction uses the tensor ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L225-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L225-L234

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc

theorem GlobalTheory.CompanionTheory.CotLoc.tensor_ext {R R' W N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W]
    [Module R W] [AddCommGroup N] [Module R' N] {f g : (R' ⊗[R] W) →ₗ[R'] N}
    (h : ∀ w, f (1 ⊗ₜ w) = g (1 ⊗ₜ w)) : f = g := by sorry
