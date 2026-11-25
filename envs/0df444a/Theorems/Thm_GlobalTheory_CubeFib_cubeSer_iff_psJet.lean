-- Prove2me | Theorems.Thm_GlobalTheory_CubeFib_cubeSer_iff_psJet
-- name    : GlobalTheory.CubeFib.cubeSer_iff_psJet
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:43.1994+00:00
-- url     : https://prove2.me/theorems/789065d8-ad37-46dd-9c5d-acf3be496bc4
-- title:
--   Cube Fib: cube Ser iff ps Jet
-- statement:
--   The Cube Fib construction uses the cube Ser iff ps Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L113-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
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
open GlobalTheory GlobalTheory.CubeFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type} [CommRing k] {d g : ℕ}

theorem GlobalTheory.CubeFib.cubeSer_iff_psJet (hd : 0 < d) {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G) (i : L.L.ι) (Φ : PS k 3 d) :
    CubeSer c x i Φ ↔ ∀ m : ℕ,
      ∃ h : (⊤ : (Sp (JetR k (Fin 3 × Fin d) m)).Opens) ≤ (jet3 x m).left ⁻¹ᵁ (Theta G L.L).U (fun _ => i),
        (Semi.res h (pullU (jet3 x m).left _ (c.t.s fun _ => i))).val =
          (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) m))).inv.hom (psJet m Φ) := by sorry
