-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_bijective_of_surjective_of_VB
-- name    : GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:17.71771+00:00
-- url     : https://prove2.me/theorems/ebdd6fff-70fc-4138-8515-3b91ed2acf36
-- title:
--   Wedge Of: bijective of surjective of VB
-- statement:
--   The Wedge Of construction uses the bijective of surjective of VB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BijectiveOfSurjectiveSameRank.lean#L8-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BijectiveOfSurjectiveSameRank.lean#L8-L48

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BijectiveOfSurjectiveSameRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf

theorem GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B,
    Function.Surjective f → Function.Bijective f := by sorry
