-- Prove2me | Theorems.Thm_GlobalTheory_RelExp_exists_local_exp
-- name    : GlobalTheory.RelExp.exists_local_exp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:42.197664+00:00
-- url     : https://prove2.me/theorems/afe38439-2fce-4f2b-a458-50fc8a92e552
-- title:
--   Rel Exp: exists local exp
-- statement:
--   The Rel Exp construction uses the exists local exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L87-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AnalyticAtCoordinateZero.lean#L87-L145

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

theorem GlobalTheory.RelExp.exists_local_exp [IsCommMonObj G]
    (hexp : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)))
    (hy : HolAt y b₀) (hOo : IsOpen O) (hU : ⊤ ≤ pt (1 : Over.mk (y b₀) ⟶ G) ⁻¹ᵁ U)
    (hO : (b₀, crd U f (pt (1 : Over.mk (y b₀) ⟶ G))) ∈ O) {s : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hs1 : HolAt (fun q : (Fin m → ℂ) × (Fin g → ℂ) => pt (s q.1 q.2)) (b₀, 0))
    (hs2 : ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), crd0 t (s q.1 q.2) = q.2)
    (hs3 : ∀ b (a : Over.mk (y b) ⟶ G), ⊤ ≤ pt a ⁻¹ᵁ U → (b, crd U f (pt a)) ∈ O → s b (crd0 t a) = a) :
    ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧
      (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, 0, 0),
        s q.1 (E (q.1, q.2.1 + q.2.2)) = s q.1 (E (q.1, q.2.1)) * s q.1 (E (q.1, q.2.2)) := by sorry
