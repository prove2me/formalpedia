-- Prove2me | Theorems.Thm_GlobalTheory_SeriesValue_LimVal_mul
-- name    : GlobalTheory.SeriesValue.LimVal.mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:22:33.456563+00:00
-- url     : https://prove2.me/theorems/210e2d47-6c5f-5f62-bb3c-4994c16045ca
-- title:
--   Lim Val: mul
-- statement:
--   The Lim Val construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L302-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_FamGerm_Pt1_Transl_mul
import Theorems.Thm_GlobalTheory_HodgeTateStep_HasDlog_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}
variable {O : Type} [CommRing O] [Algebra V O]
variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]
variable {p : O}

theorem GlobalTheory.SeriesValue.LimVal.mul (hx : IsUnivChart G d x) {L : Fin d → PS V 2 d} (hL : IsLawOf x L)
    (hu : ev (n := 2) ![fun i => MvPowerSeries.map (algebraMap V O) (L i)] u =
      ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0] u * ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1] u)
    {g g' : specV (algebraMap V O) A ⟶ G} {k k' : A}
    (h : LimVal x u p g.left k) (h' : LimVal x u p g'.left k') : LimVal x u p (g * g').left (k * k') := by sorry
