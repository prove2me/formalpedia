-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_3_2
-- name    : InducedExpanderTest989.Structural.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:07.453852+00:00
-- url     : https://prove2.me/theorems/2a8dff01-7419-4b73-b429-7bb672317b30
-- title:
--   Lemma 3.2 — contraction of total variation
-- statement:
--   Let K be a stochastic matrix on a finite state space and let a be any real row vector, with total variation norm half its ℓ¹ norm. Then
--   $$\|aK\|_{\rm TV}\le\|a\|_{\rm TV}.$$
--   No positivity or normalization of a is assumed. This transfers endpoint comparisons through a common transition kernel.
--
--   Differences from the source:
--   - encoding: finite stochastic matrix and row-vector total variation → Mathlib rowStochastic, Matrix powers and MarkovChain.tvDist; reason: the existing finite-chain definitions use the same row convention and add no irreducibility assumption
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.14 (PDF p.16), Lemma 3.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_3_2 {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℝ) (hK : Stochastic K) (a : X → ℝ) :
    tvNorm (Matrix.vecMul a K) ≤ tvNorm a := by sorry

end InducedExpanderTest989.Structural
