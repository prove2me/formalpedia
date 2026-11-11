-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_8
-- name    : GainShareOpt.StochBalance.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:18.381035+00:00
-- url     : https://prove2.me/theorems/2c5b4e75-98f8-4157-bd5d-1a75b5f933b2
-- title:
--   Lemma 8 — on $F_2$ the infimum (6) is the $\psi=1$ minimum (51)
-- statement:
--   For every $f\in F_2$, the value of (6) equals the minimum
--   $$\min_{\ell\ge0,\ \tilde\psi\in[0,1]}\Bigl\{\int_0^\ell e^{-z}f(z)\,dz+\int_\ell^{\ell+\tilde\psi}e^{-z}\,dz+(1-\tilde\psi)\bigl(1-f(\ell+\tilde\psi)\bigr)\Bigr\}, \tag{51}$$
--   and this minimum is attained.
--
--   It is the first step of Proposition 4.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: L[f] = min_{ℓ≥0, ψ̃∈[0,1]} {…} → IsLeast of the set of ψ = 1 test values with value canonicalL f; reason: the printed min asserts attainment and equality; IsLeast states both
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 29, Lemma 8, (51)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Lemma 8: for `f ∈ F2`, the value (6) is the minimum (51) of the `ψ = 1` tests over
`ℓ ≥ 0`, `ψ̃ ∈ [0, 1]` (attained). -/
theorem lemma_8 (f : ℝ → ℝ) (hf : f ∈ F2) :
    IsLeast {r | ∃ ℓ ψt : ℝ, 0 ≤ ℓ ∧ ψt ∈ Set.Icc (0 : ℝ) 1 ∧ r = partialTest f ℓ ψt}
      (canonicalL f) := by sorry

end GainShareOpt.StochBalance
