-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_vb_exteriorPower_two
-- name    : GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:22.638631+00:00
-- url     : https://prove2.me/theorems/d656a776-a960-4c58-b4be-18be4767abac
-- title:
--   Wedge Of: vb exterior Power two
-- statement:
--   The Wedge Of construction uses the vb exterior Power two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorSquareVectorBundleRank.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorSquareVectorBundleRank.lean#L14-L43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRank
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf

theorem GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by sorry
