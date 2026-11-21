-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_D
-- name    : MultibrotCorr.theorem_D
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:31:44.04399+00:00
-- url     : https://prove2.me/theorems/b211a201-3967-4884-9213-50ac7f7c9a43
-- title:
--   Theorem D (arXiv:2509.05682) — repelling cycle, $J_a=K_a$, backward-orbit density
-- statement:
--   Theorem D of the companion paper: if $a$ is a Misiurewicz point, then the critical point is preperiodic to a repelling cycle $\alpha_a$ contained in $K_a$ (existence of the canonical orbit-and-branch data with a repelling cycle); moreover $J_a=K_a$, and $K_a$ is the closure of the backward orbit $\bigcup_{n\ge0}\mathbf{f}_a^{-n}(0)$. In particular repelling cycles are dense in $K_a$.
-- source:
--   C. Siqueira, Misiurewicz points and subhyperbolicity in unicritical algebraic correspondences, https://arxiv.org/abs/2509.05682, Theorem D; as cited in arXiv:2509.07266, Sections 1.4, 1.6, 5.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_D (e : UnicriticalExponent) (a : ℂ) (ha : IsMisiurewicz e a) :
    (∃ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ),
      IsMisiurewiczOrbitData e a ℓ n z φ U) ∧
    juliaSet e a = filledJulia e a ∧
    filledJulia e a = closure (⋃ n : ℕ, backwardOrbitSet e a n) := by sorry
end MultibrotCorr
