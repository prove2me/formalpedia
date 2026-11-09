-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_uniform_potential_contraction
-- name    : HardCoreLocalSampling.Local.uniform_potential_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:25.762142+00:00
-- url     : https://prove2.me/theorems/126be3b7-d5c6-4033-9400-8190bb281e96
-- title:
--   Lemma 7 — Uniform potential contraction
-- statement:
--   There is an effectively computable rational $\rho\in(0,1)$, computed from $\Delta$ and $\lambda$, such that for every $0\le d\le b=\Delta-1$ and every $y\in[0,\infty)^d$,
--
--   $$
--   \sum_{i=1}^d|\partial_iF_d(y)|\le\rho.
--   $$
--
--   This is the contraction that keeps the expected number of recursive children below one; it holds on the whole nonnegative orthant, not only near true messages. The case $d=0$ is the empty sum.
--
--   Differences from the source:
--   - reading: there is an effectively computable rational ρ → one Computable function maps Δ and the code of λ to ρ; reason: effective is read as uniformly computable in the parameters, the stronger reading, which the source's bisection provides; a single fixed pair is computable trivially, so the fixed-parameter reading would say nothing
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 7, eq. (3), printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 7, printed p.6 (PDF p.7), eq. (3).
`ρ` is computed from `Δ` and the code of `λ`, and works for every `0 ≤ d ≤ b` and
`y ∈ [0,∞)^d`. -/
theorem uniform_potential_contraction :
    ∃ compute : ℕ × RatCode → RatCode, Computable compute ∧
      ∀ (Delta : ℕ) (lam : ℚ), Standing Delta lam →
        IsContractionConstant Delta lam (ratOfCode (compute (Delta, codeOfRat lam))) := by sorry

end HardCoreLocalSampling.Local
