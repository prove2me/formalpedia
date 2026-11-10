-- Prove2me | Theorems.Thm_LRTempElim_eq_53
-- name    : LRTempElim.eq_53
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:15.714029+00:00
-- url     : https://prove2.me/theorems/83ea3876-945e-4b3a-961e-b1becaf46a63
-- title:
--   Eq. (53): the influence bracket in the centered basis is affine in $a$ with a moment envelope
-- statement:
--   Write $W=(X_0,X_1)=(U-a/2,V+a/2)$, $Z_t=(1-t)U+tV$, $\mu_t=(t-\tfrac12)a$, $c_t=(1-t)^2+t^2$, $c'_t=\frac d{dt}c_t$, and let the true score at the bridge point be
--   $$
--   s^\star_t=\frac{aZ_t}{c_t}+\frac{c'_t}{2c_t^2}(Z_t^2-c_t).
--   $$
--   Let
--   $$
--   \beta_t=\begin{pmatrix}0\\a+V-U\\2Z_t(a+V-U)\end{pmatrix}-\begin{pmatrix}1\\Z_t\\Z_t^2\end{pmatrix}s^\star_t .
--   $$
--   Then, with $\phi=(1,x,x^2)$ and $L_{a,t}$ the change-of-basis matrix with $\phi(\mu_t+z)=L_{a,t}(1,z,z^2)^\top$:
--
--   1. for every $a$, $t\in[0,1]$ and $U,V$: $X_t=\mu_t+Z_t$, the fitted score $\phi(X_t)^\top v_t$ equals $s^\star_t$, and the bracket $D_t(W)-\Phi_t(W)\Phi_t(W)^\top v_t$ of the influence function equals $L_{a,t}\beta_t$, i.e. $\beta_t$ is the bracket in the centered basis;
--   2. $\beta_t$ is affine in $a$;
--   3. there is an envelope $F(U,V)$, free of $t$ and $a$ and with all moments finite when $U,V$ are independent standard Gaussians, such that every coordinate of $\beta_t$ is bounded by $(1+|a|)F(U,V)$ for all $t\in[0,1]$.
--
--   This is the step that makes the path influence function polynomial in $a$ with Gaussian-moment coefficients.
--
--   Differences from the source:
--   - reading: "in this basis the bracket in (51) is (53)" → the original-basis bracket equals L_{a,t} times the vector (53); reason: coordinates with respect to the centered basis (1, Z_t, Z_t²)
--   - reading: "which is linear in a with Gaussian polynomial coefficients and a uniform moment envelope" → β is affine in a, and |β_i| ≤ (1 + |a|)F(U, V) for t ∈ [0,1] with F free of t and a and in every L^r(N(0,1) ⊗ N(0,1)); reason: "linear" in the sense of degree one; the envelope is the uniform-in-t moment control the sentence asserts
--   - encoding: the true score s⋆_t → an explicit clause ϕ(X_t)⊤v_t = s⋆_t; reason: the sentence uses that the fitted score equals the true score
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), §A.2.3, eq. (53), p.20 (pdf p.22)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-- **Eq. (53)**: the influence bracket in the centered basis. Chen, Wu, Yang, Zeng,
*Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), §A.2.3, eq. (53), p.20 (pdf p.22).

"The true score is `s⋆_t = aZ_t/c_t + c′_t/(2c_t²)(Z_t² − c_t)`. In this basis the bracket in (51) is
`(0, a + V − U, 2Z_t(a + V − U))⊤ − (1, Z_t, Z_t²)⊤ s⋆_t`, (53) which is linear in a with Gaussian
polynomial coefficients and a uniform moment envelope."

**Formalization Note.** Pointwise in `W = (X₀, X₁) = (U − a/2, V + a/2)`, `Z_t = (1 − t)U + tV`,
`µ_t = bridgeMean a t`, `c_t = bridgeVar t`, `c′_t = deriv bridgeVar t`, `t ∈ [0, 1]`. The bracket of
(51) is `D_t(W) − Φ_t(W)Φ_t(W)⊤v_t` (`pathBracket`). "In this basis" means coordinates with respect
to the centered basis `(1, Z_t, Z_t²)`: since `ϕ(µ_t + z) = L ϕ(z)` with
`L = [[1,0,0],[µ_t,1,0],[µ_t²,2µ_t,1]]`, the original-basis bracket equals `L` times the
centered-basis vector (53). The clause `Φ_t⊤v_t = s⋆_t` records that the fitted score at `X_t` is
the true score. The trailing remark is formalized as two clauses: the centered vector is affine
in `a` (`β(a) = β(0) + a(β(1) − β(0))`), and there is one envelope `F(U, V)`, free of `t` and `a`
and with every moment finite under `U, V` i.i.d. `N(0, 1)`, such that every coordinate is at most
`(1 + |a|)F(U, V)` in absolute value for all `t ∈ [0, 1]`. -/
theorem eq_53 :
    let γ : Measure ℝ := gaussianReal 0 1
    let L : ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun a t =>
      !![1, 0, 0; bridgeMean a t, 1, 0; bridgeMean a t ^ 2, 2 * bridgeMean a t, 1]
    let Z : ℝ → ℝ → ℝ → ℝ := fun t U V => (1 - t) * U + t * V
    let sStar : ℝ → ℝ → ℝ → ℝ → ℝ := fun a t U V =>
      a * Z t U V / bridgeVar t +
        deriv bridgeVar t / (2 * bridgeVar t ^ 2) * (Z t U V ^ 2 - bridgeVar t)
    let β : ℝ → ℝ → ℝ → ℝ → Fin 3 → ℝ := fun a t U V =>
      ![0, a + V - U, 2 * Z t U V * (a + V - U)] - sStar a t U V • ![1, Z t U V, Z t U V ^ 2]
    (∀ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ U V : ℝ,
      bridge t (U - a / 2, V + a / 2) = bridgeMean a t + Z t U V ∧
        phi3 (bridge t (U - a / 2, V + a / 2)) ⬝ᵥ vCoef phi3 a t = sStar a t U V ∧
        pathBracket phi3 a t (U - a / 2, V + a / 2) = L a t *ᵥ β a t U V) ∧
    (∀ a t U V : ℝ, β a t U V = β 0 t U V + a • (β 1 t U V - β 0 t U V)) ∧
    (∃ F : ℝ × ℝ → ℝ, (∀ r : ℕ, MemLp F (r : ENNReal) (γ.prod γ)) ∧
      ∀ a : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ U V : ℝ, ∀ i : Fin 3,
        |β a t U V i| ≤ (1 + |a|) * F (U, V)) := by sorry

end LRTempElim
