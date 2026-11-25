-- Prove2me | Theorems.Thm_GlobalTheory_SeriesValue_existsUnique_jet
-- name    : GlobalTheory.SeriesValue.existsUnique_jet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:49:16.38196+00:00
-- url     : https://prove2.me/theorems/55773ea8-ba84-4c17-85a9-9d119ec568e3
-- title:
--   Series Value: exists Unique jet
-- statement:
--   The Series Value construction uses the exists Unique jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueJet.lean#L17-L49

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

theorem GlobalTheory.SeriesValue.existsUnique_jet [IsLocalRing V] {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (q : A →ₐ[V] B) (hq : Function.Surjective q) {m : ℕ}
    (hJ : (RingHom.ker q) ^ (m + 1) = ⊥) (y : sp (R₀ := V) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃! ψ : JetR V (Fin d) m →ₐ[V] A, (∀ j, q (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m := by sorry
