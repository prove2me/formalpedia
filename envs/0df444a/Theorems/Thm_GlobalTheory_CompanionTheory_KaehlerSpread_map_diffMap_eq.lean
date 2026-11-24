-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_map_diffMap_eq
-- name    : GlobalTheory.CompanionTheory.KaehlerSpread.map_diffMap_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:01.966729+00:00
-- url     : https://prove2.me/theorems/32c130a2-e714-487e-9b54-7c6ee1a8852f
-- title:
--   Kaehler Spread: map diff Map eq
-- statement:
--   The Kaehler Spread construction uses the map diff Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L13-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential

theorem GlobalTheory.CompanionTheory.KaehlerSpread.map_diffMap_eq (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by sorry
