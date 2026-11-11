-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_18
-- name    : LindbladQueryOptimal.Simulation.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:42.264743+00:00
-- url     : https://prove2.me/theorems/cc322950-c595-4834-a5d5-8524dd1f0d8d
-- title:
--   Lemma 18 — Factorial Degree Requirement
-- statement:
--   For every fixed $B\ge1$ there is a positive constant $C_B$, depending only on $B$, such that every $\tau\ge0$, $0<\epsilon\le1/2$, and integer $q\ge C_Bc(\tau,\epsilon)$ satisfy
--   $$B\sqrt\tau\left(B\sqrt{\tau/q}\right)^q\le\epsilon.$$
--   Here $c$ is exactly Eq. (33), with its separate zero-time value. The constant is chosen before time, precision and degree, so the bound is uniform over those parameters.
--
--   Differences from the source:
--   - encoding: a degree and a constant depending only on the fixed B → a natural degree and a positive existential constant before τ, ε and q; reason: makes the degree domain and the source uniformity explicit; the positive threshold excludes q=0
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 18, p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_18 (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ ε : ℝ) (q : ℕ),
      0 ≤ τ → 0 < ε → ε ≤ 1/2 → C * queryScale τ ε ≤ q →
      B * Real.sqrt τ * (B * Real.sqrt (τ/q))^q ≤ ε := by sorry

end LindbladQueryOptimal.Simulation
