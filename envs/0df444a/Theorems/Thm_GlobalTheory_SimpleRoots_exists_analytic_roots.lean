-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_exists_analytic_roots
-- name    : GlobalTheory.SimpleRoots.exists_analytic_roots
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:02.30842+00:00
-- url     : https://prove2.me/theorems/ee9b7fba-a91f-4900-967b-745251f48041
-- title:
--   Simple Roots: exists analytic roots
-- statement:
--   The Simple Roots construction uses the exists analytic roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L61-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L61-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by sorry
