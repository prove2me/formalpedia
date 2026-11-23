-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually_near
-- name    : GlobalTheory.RelExp.HolAt.eventually_near
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:37.25614+00:00
-- url     : https://prove2.me/theorems/3c0149e7-b18d-4ce4-80c2-d1c542dbbf02
-- title:
--   Hol At: eventually near
-- statement:
--   The Hol At construction uses the eventually near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L76-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtCoordinateZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {X : Scheme.{0}} {G : Over X}
variable [GrpObj G] {g m n : ℕ} {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} {b₀ : Fin m → ℂ} {U : G.left.Opens}
  {t : Fin g → Γ(G.left, U)} {f : Fin n → Γ(G.left, U)} {O : Set ((Fin m → ℂ) × (Fin n → ℂ))}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {β : E → (Fin m → ℂ)}
  {a : ∀ w, Over.mk (y (β w)) ⟶ G} {w₀ : E}

theorem GlobalTheory.RelExp.HolAt.eventually_near (ha : HolAt (fun w => pt (a w)) w₀) (hβ : ContinuousAt β w₀) (h1 : a w₀ = 1)
    (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y (β w₀)) ⟶ G) ⁻¹ᵁ U)
    (hO : (β w₀, crd U f (pt (1 : Over.mk (y (β w₀)) ⟶ G))) ∈ O) :
    ∀ᶠ w in 𝓝 w₀, ⊤ ≤ pt (a w) ⁻¹ᵁ U ∧ (β w, crd U f (pt (a w))) ∈ O := by sorry
