-- Prove2me | Theorems.Thm_GlobalTheory_T_jetChart_coordinates_unique_commGroup
-- name    : GlobalTheory.T.jetChart_coordinates_unique_commGroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:30.333511+00:00
-- url     : https://prove2.me/theorems/3adb98c6-cafc-424c-a168-3cd025b81eee
-- title:
--   T: jet Chart coordinates unique comm Group
-- statement:
--   The T construction uses the jet Chart coordinates unique comm Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetChartCoordinatesUniqueCommGroupStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetChartCoordinatesUniqueCommGroupStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.jetChart_coordinates_unique_commGroup : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ ψ ψ' : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → spMap ψ ≫ x m = spMap ψ' ≫ x m → ψ = ψ' := by sorry
