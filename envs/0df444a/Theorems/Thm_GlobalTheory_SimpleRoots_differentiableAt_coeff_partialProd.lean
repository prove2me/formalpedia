-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_differentiableAt_coeff_partialProd
-- name    : GlobalTheory.SimpleRoots.differentiableAt_coeff_partialProd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:07.037985+00:00
-- url     : https://prove2.me/theorems/e3940073-1c49-479d-816a-69e129b6b809
-- title:
--   Simple Roots: differentiable At coeff partial Prod
-- statement:
--   The Simple Roots construction uses the differentiable At coeff partial Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L68-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L68-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SimpleRoots
open Polynomial
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.differentiableAt_coeff_partialProd {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {u : Set ((Fin d → ℂ) × ℂ)} {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0)
    (hu : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 → ∀ᶠ w in 𝓝 (x₀, y),
      (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 → (w ∈ u ↔ (x₀, y) ∈ u)) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (partialProd p u x).coeff k) x₀ := by sorry
