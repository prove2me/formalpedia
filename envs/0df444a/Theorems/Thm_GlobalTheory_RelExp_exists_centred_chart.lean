-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_exists_centred_chart
-- name    : GlobalTheory.RelExp.exists_centred_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:16.998942+00:00
-- url     : https://prove2.me/theorems/03c6835b-95c9-44bb-a72e-82488a2c1e32
-- title:
--   Rel Exp: exists centred chart
-- statement:
--   The Rel Exp construction uses the exists centred chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L27-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L27-L60

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

theorem GlobalTheory.RelExp.exists_centred_chart (hy : HolAt y b₀) {N : Set ((Fin m → ℂ) × (Fin g → ℂ))}
    {σ : (Fin m → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} (hN : IsOpen N)
    (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U) (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O)
    (hσ : IsHolTo N σ) (hσN : ∀ q ∈ N, σ q ≫ G.hom = y q.1 ∧ ⊤ ≤ σ q ⁻¹ᵁ U ∧ ∀ i, valAt' (σ q) U (t i) = q.2 i)
    (hinv : ∀ (b : Fin m → ℂ) (x : Sp ℂ ⟶ G.left), x ≫ G.hom = y b → ⊤ ≤ x ⁻¹ᵁ U → (b, crd U f x) ∈ O →
      (b, crd U t x) ∈ N ∧ σ (b, crd U t x) = x) :
    ∃ s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G),
      HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2) ∧
      ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a := by sorry
