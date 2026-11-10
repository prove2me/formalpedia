-- Prove2me | Theorems.Thm_LRTempElim_proposition_A_2
-- name    : LRTempElim.proposition_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:07.811496+00:00
-- url     : https://prove2.me/theorems/9db871b0-3582-4927-ae84-99b76fe8756f
-- title:
--   Proposition A.2: $\pi/2$ representation bias of the linear-feature readout
-- statement:
--   Let $Q=N(-a/2,1)$, $P=N(a/2,1)$ and let $X_t=(1-t)X_0+tX_1$ be the independent linear bridge, $(X_0,X_1)\sim Q\otimes P$. The continuous analytic readout is $m=\int_0^1 M_t^{-1}b_t\,dt$ with $M_t=\mathbb E[\phi(X_t)\phi(X_t)^\top]$ and $b_t=\mathbb E[J_\phi(X_t)(X_1-X_0)]$, and the fitted function is $f(x)=\phi(x)^\top m$. For every real $a$:
--
--   1. with $\phi(x)=(1,x)^\top$,
--   $$
--   m=\Big(0,\ \frac\pi2 a\Big)^\top,\qquad f(x)=\frac\pi2\,ax,
--   $$
--   whereas the target is $\ell^\star(x)=ax$;
--   2. with $\phi(x)=(1,x,x^2)^\top$, $m=(0,a,0)^\top$ and $f=\ell^\star$.
--
--   The second part says that the quadratic features calibrate the path estimator: its population target is the true log-ratio coefficient. This is the centre of the path estimator's central limit theorem in the goal theorem.
--
--   Differences from the source:
--   - encoding: continuous analytic readout with exact time integration → `readout ϕ a` = interval integral over [0,1] of M_t⁻¹b_t with b_t = E[J_ϕ(X_t)(X₁ − X₀)]; reason: the paper's definition (41) of the readout
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Proposition A.2, eq. (25), p.15 (pdf p.17)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Proposition A.2** (π/2 representation bias). Chen, Wu, Yang, Zeng, *Likelihood-Ratio
Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027 submission (manuscript
of 2026-11-03, sha256 eee65139…), Proposition A.2, eq. (25), p.15 (pdf p.17).

"Let `Q = N(−a/2, 1)`, `P = N(a/2, 1)`, and let `X_t = (1 − t)X₀ + tX₁` be the independent linear
bridge. With `ϕ(x) = (1, x)⊤` and exact time integration, the continuous analytic readout is
`m = (0, π/2 a)⊤`, `f(x) = π/2 ax`, (25) whereas the target is `ℓ⋆(x) = ax`. With
`ϕ(x) = (1, x, x²)⊤`, the analytic readout is `m = (0, a, 0)⊤` and `f = ℓ⋆`."

**Formalization Note.** The readout is `m = ∫₀¹ M_t⁻¹b_t dt` with `M_t = E[ϕ(X_t)ϕ(X_t)⊤]` and
`b_t = E[J_ϕ(X_t)(X₁ − X₀)]` (`readout`, eq. (41)); `f(x) = ϕ(x)⊤m`. Stated for every real `a`. -/
theorem proposition_A_2 (a : ℝ) :
    readout phi2 a = ![0, Real.pi / 2 * a] ∧
      (∀ x : ℝ, phi2 x ⬝ᵥ readout phi2 a = Real.pi / 2 * a * x) ∧
      readout phi3 a = ![0, a, 0] ∧
      (∀ x : ℝ, phi3 x ⬝ᵥ readout phi3 a = a * x) := by sorry

end LRTempElim
