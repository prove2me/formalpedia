-- Prove2me | Theorems.Thm_GlobalTheory_SeriesValue_exists_limVal
-- name    : GlobalTheory.SeriesValue.exists_limVal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:17.104884+00:00
-- url     : https://prove2.me/theorems/6ae15b8e-c9b3-4853-9f80-b13015030ea5
-- title:
--   Series Value: exists lim Val
-- statement:
--   The Series Value construction uses the exists lim Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L325-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L325-L358

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
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

theorem GlobalTheory.SeriesValue.exists_limVal [IsLocalRing V] (hx : IsUnivChart G d x) (u : PS O 1 d) (p : O)
    [IsPrecomplete (Ideal.span {algebraMap O A p}) A] (I : Ideal A) {m : ℕ}
    (hI : I ^ m ≤ Ideal.span {algebraMap O A p}) (g : specV (algebraMap V O) A ⟶ G)
    (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : specV (algebraMap V O) A ⟶ G).left) :
    ∃ k, LimVal x u p g.left k := by sorry
