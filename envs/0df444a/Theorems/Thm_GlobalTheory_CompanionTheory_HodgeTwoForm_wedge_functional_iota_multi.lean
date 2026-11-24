-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_iota_multi
-- name    : GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_iota_multi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:52.030885+00:00
-- url     : https://prove2.me/theorems/47bb1247-1ff1-478d-9853-ffc4d0ea7e5f
-- title:
--   Hodge Two Form: wedge functional iota multi
-- statement:
--   The Hodge Two Form construction uses the wedge functional iota multi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeFunctionalTwoFormNaturality.lean#L36-L39

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

theorem GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_iota_multi (L : Fin n → Module.Dual A M) (i j : Fin n) (a b : M) :
    L2 L i j (exteriorPower.ιMulti A 2 ![a, b]) = L i a * L j b - L j a * L i b := by sorry
