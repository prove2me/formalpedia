-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_UniversalJets_rename
-- name    : GlobalTheory.TorsionCompare.UniversalJets.rename
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:16.765727+00:00
-- url     : https://prove2.me/theorems/0c9ba30a-21fe-45cf-8888-f2af58ca92ca
-- title:
--   Universal Jets: rename
-- statement:
--   The Universal Jets construction uses the rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L155-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L155-L185

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]

theorem GlobalTheory.TorsionCompare.UniversalJets.rename {σ σ' : Type} (e : σ → σ') (e' : σ' → σ)
    (h : ∀ j, e' (e j) = j) (h' : ∀ j, e (e' j) = j)
    {x : ∀ m : ℕ, algOver R (JetR R σ m) ⟶ G} (hx : UniversalJets G x) :
    UniversalJets G (renameChart e x) := by sorry
