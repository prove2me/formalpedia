-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_theorem_A_9
-- name    : LpSubspaceCoreset.SmallP.theorem_A_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:16.93792+00:00
-- url     : https://prove2.me/theorems/72d633f4-8d51-4202-b5d0-7fc4e2c2c564
-- title:
--   Theorem A.9 — Lewis-weight Rademacher bound for low-rank terms
-- statement:
--   Fix $1\le p<2$. There is $C_p$ such that the following holds. Let $r\ge1$, $H$ a real Hilbert space, and for $i\in[n]$ let $w_i\ge0$ and $y_i\in\mathbb R^r$ satisfy $\sum_iw_iy_iy_i^\top=I_r$, $\|y_i\|_2=1$ whenever $w_i>0$, and $y_i=0$ whenever $w_i=0$. Let $q$ be a probability distribution with $q_i>0$ whenever $w_i>0$ and put $K=\max_{w_i>0}w_i/q_i$. For a linear map $T:\mathbb R^r\to H$ with $S_T=\sum_jw_j\|Ty_j\|^p>0$ put $h_T(i)=w_i\|Ty_i\|^p/(q_iS_T)$ if $w_i>0$ and $0$ if $w_i=0$; zero-cost maps are assigned the zero function. Then for every sample size $m$ (samples drawn from $q$)
--   $$R^{\mathrm{abs}}_m(\{h_T\})\le C_p\,(\log(n+r+m+K+2))^{C_p}\Big(\sqrt{K/m}+K/m\Big).\qquad(A.20)$$
--   It controls the low-rank coordinate of the loss in Theorem 3.1 and gives the case $R=0$ directly.
--
--   Differences from the source:
--   - reading: C_p polylog(n + r + m + K + 2) → C·(log(n + r + m + K + 2))^C with one C = C_p; reason: polylog with an explicit p-dependent constant
--   - encoding: K = max_{w_i>0} w_i/q_i → ⨆ over i of (w_i/q_i if w_i > 0 else 0); reason: the same value since every term is nonnegative and some w_i > 0
--   - encoding: R^abs_m → radAbs: finite sum over [n]^m weighted by Π q_{I_s} of the sign average, suprema in [0, ∞]; reason: a finite expectation, no junk value
--   - encoding: a linear map T : ℝ^r → H, H a Hilbert space → T : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H, H : Type with InnerProductSpace ℝ H and CompleteSpace H; reason: Lean's real Hilbert space; every linear map out of ℝ^r is continuous
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 47–48, Theorem A.9

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Process

namespace LpSubspaceCoreset.SmallP

/-- **Theorem A.9** (Lewis-weight bound for low-rank terms), pp. 47–48.

Fix `1 ≤ p < 2`; there is `C_p` such that the following holds. Let `r ≥ 1`, `H` a real Hilbert
space, and for `i ∈ [n]` let `w_i ≥ 0` and `y_i ∈ ℝ^r` with `Σ_i w_i y_i y_i^⊤ = I_r`, `‖y_i‖₂ = 1`
whenever `w_i > 0`, and `y_i = 0` whenever `w_i = 0`. Let `q` be a probability distribution with
`q_i > 0` whenever `w_i > 0`, and `K = max_{w_i > 0} w_i/q_i`. For a linear map `T : ℝ^r → H` with
`S_T = Σ_j w_j ‖T y_j‖^p > 0` put `h_T(i) = w_i ‖T y_i‖^p/(q_i S_T)` if `w_i > 0` and `0` if `w_i = 0`;
zero-cost maps get the zero function. Then for every `m`,
`R^abs_m({h_T}) ≤ C_p (log(n + r + m + K + 2))^{C_p} (√(K/m) + K/m)` (A.20), the samples drawn
from `q`. -/
theorem theorem_A_9 :
    ∀ p : ℝ, 1 ≤ p → p < 2 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n r : ℕ), 1 ≤ r →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (w : Fin n → ℝ) (y : Fin n → EuclideanSpace ℝ (Fin r)),
      (∀ i, 0 ≤ w i) →
      ∑ i, w i • Matrix.vecMulVec (WithLp.ofLp (y i)) (WithLp.ofLp (y i)) = 1 →
      (∀ i, 0 < w i → ‖y i‖ = 1) → (∀ i, w i = 0 → y i = 0) →
    ∀ q : Fin n → ℝ, IsProbLaw q → (∀ i, 0 < w i → 0 < q i) →
      let K : ℝ := ⨆ i : Fin n, if 0 < w i then w i / q i else 0
      let S : (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H) → ℝ := fun T => ∑ j, w j * ‖T (y j)‖ ^ p
      let h : (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H) → Fin n → ℝ := fun T i =>
        if 0 < S T ∧ 0 < w i then w i * ‖T (y i)‖ ^ p / (q i * S T) else 0
      ∀ m : ℕ, radAbs q (Set.range h) m ≤ ENNReal.ofReal
        (C * (Real.log (n + r + m + K + 2)) ^ C * (Real.sqrt (K / m) + K / m)) := by sorry

end LpSubspaceCoreset.SmallP
