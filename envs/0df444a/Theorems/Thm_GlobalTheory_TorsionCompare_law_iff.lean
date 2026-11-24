-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCompare_law_iff
-- name    : GlobalTheory.TorsionCompare.law_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:39.539+00:00
-- url     : https://prove2.me/theorems/b8f1bdad-c4ea-40a9-9231-4612bc9bcfb0
-- title:
--   Torsion Compare: law iff
-- statement:
--   The Torsion Compare construction uses the law iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L202-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotIsUnitNatCastOfIsLocalHom.lean#L202-L233

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
variable {d : ℕ}

theorem GlobalTheory.TorsionCompare.law_iff (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) (m : ℕ) :
    (algOverHom (substJ m F.F F.const) ≫ x m =
      (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ x m) *
        (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ x m)) ↔
    ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
      (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
      lift (algOverHom ψ₀ ≫ chartEquiv G d x m) (algOverHom ψ₁ ≫ chartEquiv G d x m) ≫ μ[G] =
        algOverHom ψ ≫ chartEquiv G d x m := by sorry
