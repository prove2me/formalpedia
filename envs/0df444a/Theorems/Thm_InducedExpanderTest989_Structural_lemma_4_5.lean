-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_5
-- name    : InducedExpanderTest989.Structural.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:04.501235+00:00
-- url     : https://prove2.me/theorems/f363293c-9639-459f-8e60-3efa4fffea19
-- title:
--   Lemma 4.5 — stopping-time potential identity
-- statement:
--   Let K be any stochastic matrix on a finite state space, started at a state x. Let τ be a stopping time for the natural observed trajectory with finite expected value, and let ν be the distribution of the stopped state. For every integer ℓ≥1, set Q_ℓ=ℓ⁻¹∑_{j<ℓ}K^j. Then
--   $$\|e_xQ_\ell-\nu Q_\ell\|_{\rm TV}\le\mathbb E_x[\tau]/\ell.$$
--   This compares two distributions propagated through the same averaging kernel, without symmetry, laziness, graph structure, or a finite horizon.
--
--   Differences from the source:
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
--   - encoding: walk trajectories, infinite hitting times and expectations → Ionescu–Tulcea path measure, ℕ∞ visit times and extended nonnegative expectations; reason: never-hit paths retain infinity; real expectations are used only where Lemma 4.2 guarantees finiteness
--   - encoding: the event τ=s is determined by X₀,…,X_s → NaturalStopping expresses prefix invariance on the discrete infinite path space; reason: on a finite state space prefix invariance is exactly measurability of each finite stopping event
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.19 (PDF p.21), Lemma 4.5; definition of stopping time p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_5 {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : Matrix X X ℝ) (hK : Stochastic K) (x : X)
    (τ : Path X → ℕ∞) (hτ : NaturalStopping τ)
    (hi : elapsedMean (pathLaw K x) τ < ⊤) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    MarkovChain.tvDist ((averaging K ℓ) x)
      (Matrix.vecMul (stoppedLaw (pathLaw K x) τ) (averaging K ℓ)) ≤
    (elapsedMean (pathLaw K x) τ).toReal / ℓ := by sorry

end InducedExpanderTest989.Structural
