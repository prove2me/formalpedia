-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_proposition_4
-- name    : GainShareOpt.StochBalance.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:27.807269+00:00
-- url     : https://prove2.me/theorems/27d23ff9-3324-477d-9872-5e7b63cd7b95
-- title:
--   Proposition 4 — on $F_2$, $L[f]=\min\{W_1,W_2\}$
-- statement:
--   For every $f\in F_2$, the value of (6) satisfies
--   $$L[f]=\min\{W_1,W_2\},\quad W_1=\int_0^1e^{-z}f(z)\,dz+e^{-1}(1-e^{-1}),\quad W_2=\min_{\ell,\tilde\psi\in[0,1],\ \ell+\tilde\psi\le1}\Psi_f(\ell,\tilde\psi).$$
--
--   This is the reduction that makes $F_2$ the setting of the auxiliary LPs, and it is used in Lemma 10.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: W2 = min over ℓ, ψ̃ ∈ [0,1], ℓ + ψ̃ ≤ 1 → W2 is the real sInf of that set; reason: the set is the continuous image of a compact set for f ∈ F2, so the infimum is the minimum
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 11, Proposition 4, (11)–(12) (proof App. C, pp. 29–30)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Proposition 4: for `f ∈ F2`, the value (6) equals `min{W1, W2}`. -/
theorem proposition_4 (f : ℝ → ℝ) (hf : f ∈ F2) : canonicalL f = min (W1 f) (W2 f) := by sorry

end GainShareOpt.StochBalance
