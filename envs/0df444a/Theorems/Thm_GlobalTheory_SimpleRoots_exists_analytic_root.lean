-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_exists_analytic_root
-- name    : GlobalTheory.SimpleRoots.exists_analytic_root
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:13:10.075073+00:00
-- url     : https://prove2.me/theorems/c1127ebb-afcc-47de-a1f7-e0ac2c47f4e8
-- title:
--   Simple Roots: exists analytic root
-- statement:
--   The Simple Roots construction uses the exists analytic root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L24-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L24-L49

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

theorem GlobalTheory.SimpleRoots.exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by sorry
