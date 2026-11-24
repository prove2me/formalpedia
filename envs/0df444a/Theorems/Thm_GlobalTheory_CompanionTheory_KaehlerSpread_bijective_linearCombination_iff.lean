-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_bijective_linearCombination_iff
-- name    : GlobalTheory.CompanionTheory.KaehlerSpread.bijective_linearCombination_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:20.844999+00:00
-- url     : https://prove2.me/theorems/d897e274-1b73-40f5-a325-688d81cd718c
-- title:
--   Kaehler Spread: bijective linear Combination iff
-- statement:
--   The Kaehler Spread construction uses the bijective linear Combination iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/KaehlerBasisSpreadsToNeighbourhood.lean#L28-L33

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

theorem GlobalTheory.CompanionTheory.KaehlerSpread.bijective_linearCombination_iff {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by sorry
