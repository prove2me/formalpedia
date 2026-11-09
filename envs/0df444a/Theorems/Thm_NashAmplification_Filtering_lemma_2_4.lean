-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_2_4
-- name    : NashAmplification.Filtering.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:30:57.453721+00:00
-- url     : https://prove2.me/theorems/9e884698-2c7e-421a-98d7-089d0cafc9bd
-- title:
--   Lemma 2.4 — symmetry and binary payoffs
-- statement:
--   Let $G$ be a finite $k$-player game with payoffs in $[0,1]$, $k\ge2$, nonempty action sets, $C\ge2$, $t\ge1$, and $\beta,\Delta\in(0,1)$. Set $q=1-\beta/2$ and $h=\Delta/4$. The payoff calculation on $A^t$ defines a symmetric binary-payoff game $H$:
--   $$U_{\pi(i)}(y\circ\pi^{-1})=U_i(y),\qquad U_i(y)\in\{0,1\}.$$
--   Here $\pi$ ranges over all player permutations and $y$ over all pure profiles. This establishes both structural requirements on the constructed game.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - generalization: rational β,Δ satisfying (2.5), with t and C selected by (2.10) and (2.23) → all real β and Δ in (0,1), every t≥1 and C≥2; reason: these structural, mass and error estimates need only the displayed ranges, not β+kΔ<δ or the particular t,C choices; every source choice specializes directly
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 2.4, PDF p. 10 (printed p. 9)

import Definitions.Def_NashAmplification_Filtering_Process

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 2.4, PDF 10; symmetry uses y ∘ π⁻¹. -/
theorem lemma_2_4 {k C t : ℕ} (hk : 2 ≤ k) (hC : 2 ≤ C) (ht : 1 ≤ t)
    {n : Fin k → ℕ} (hn : ∀ r, 0 < n r) (u : Utility n) (hu : BoundedGame u)
    (β Δ : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hΔ : Δ ∈ Set.Ioo (0 : ℝ) 1) :
    IsSymmetric (C := C) (payoff (t := t) u (1-β/2) (Δ/4)) ∧
    IsBinary (C := C) (payoff (t := t) u (1-β/2) (Δ/4)) := by sorry
end NashAmplification.Filtering
