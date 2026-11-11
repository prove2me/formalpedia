-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_9
-- name    : GainShareOpt.StochBalance.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:35.136382+00:00
-- url     : https://prove2.me/theorems/776e6994-73f3-4eef-a2ab-659d34019bec
-- title:
--   Lemma 9 — $L[f]\le\min\{\Phi_1(f),\Phi_2(f)\}$ on $F_0$
-- statement:
--   For every $f\in F_0$, the quantity (6) satisfies
--   $$L[f]\le\min\{\Phi_1(f),\Phi_2(f)\},$$
--   with $\Phi_1,\Phi_2$ the two adversarial tests (25)–(26) on the critical interval $[0,\tau(f)]$.
--
--   It gives the upper half $\Gamma(F_0)\le\gamma^*$ of Theorem 6.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: Φ2(f) = min over ℓ, ψ̃ ∈ [0,1], ℓ + ψ̃ ≤ τ(f) → real sInf of that set; reason: continuous image of a compact set for f ∈ F0
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 46, Lemma 9

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Lemma 9: for `f ∈ F0`, the value (6) is at most `min{Φ1(f), Φ2(f)}`. -/
theorem lemma_9 (f : ℝ → ℝ) (hf : f ∈ F0) : canonicalL f ≤ min (Phi1 f) (Phi2 f) := by sorry

end GainShareOpt.StochBalance
