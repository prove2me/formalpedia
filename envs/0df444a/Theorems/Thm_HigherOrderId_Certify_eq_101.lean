-- Prove2me | Theorems.Thm_HigherOrderId_Certify_eq_101
-- name    : HigherOrderId.Certify.eq_101
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:18:56.20114+00:00
-- url     : https://prove2.me/theorems/dfb9f438-670f-46ae-88ef-966c6a255a17
-- title:
--   §C.2, Eq. (101) — ‖Σ^eff_m‖_F ≥ c₀ v_N √(d² + m⁶) for every full-rank design in 𝔇_{d,m}(α), and ‖Γ_m‖_F ≤ C₀ v_N √(d² + m⁶) for the weighted-frame completion
-- statement:
--   There are universal constants $c_0,C_0>0$ such that the following holds for every $d\ge10$, $0\le m\le m_d$, $0<\alpha\le1/2$, $\sigma>0$ and budget $N$, with $v_N=\sigma^2(d-m)/(N\alpha^2)$.
--
--   1. For every design in $\mathfrak D_{d,m}(\alpha)$ that is full rank (positive definite Fisher information $I_{\mathrm{full}}$ of the complete value–gradient release), the covariance $\Sigma^{\mathrm{eff}}_m=I_{\mathrm{full}}^{-1}$ of the generalized least-squares sufficient statistic for $\vartheta$ (coordinates (99)) satisfies
--   $$\|\Sigma^{\mathrm{eff}}_m\|_F\ge c_0v_N\sqrt{d^2+m^6}.$$
--   2. When $N/E$ is a positive integer, let $\Gamma_m$ be the covariance, in coordinates (99), of the explicit estimator of Appendix B: $\hat b$ with covariance $(\sigma^2/N)I_d$, and the completion $\widehat Q$ of Lemma B.5 built from the full span ($m=0$) or from the weighted frame $U=U_w$, $w=m^{1/4}$ ($m\ge1$) with $[U,V_{\mathrm{env}}]$ orthogonal. Then
--   $$\|\Gamma_m\|_F\le C_0v_N\sqrt{d^2+m^6}.$$
--
--   The two inequalities feed Lemma C.1 with $\Sigma=\Sigma^{\mathrm{eff}}_m$ (converse) and $\Sigma=\Gamma_m$ (achievability) in the proof of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: Σ^eff_m, the covariance of the generalized least-squares sufficient statistic for ϑ; "a full-rank design" → the inverse of the full value–gradient Fisher information matrix in coordinates (99); I_full positive definite; reason: in a full-rank Gaussian linear model with known covariance the GLS statistic has covariance I⁻¹
--   - generalization: Γ_m for the explicit orthogonal decomposition [U, V_env] of Appendix B → for U = U_w (w = m^{1/4}) with any row placement ι, and every V_env completing U to an orthogonal matrix (any orthogonal V_env when m = 0); reason: the law of the completion estimator is unchanged by V_env ↦ V_env O (O orthogonal) and by row permutations, so the bound for all of them specializes to the paper's choice
--   - encoding: Γ_m in coordinates (99) → block diagonal: (σ²/N) I_d for b̂, and the covariance of the entries Q̂_ij (i < j); reason: b̂ = b + (σ/√N)z_b is independent of the contrast channel (55) (p. 21)
--   - encoding: c₀, C₀ universal → ∃ c₀ C₀ > 0 quantified before d, m, N, α, σ and the design; reason: explicit form of 'universal constants'
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 30, §C.2, Eq. (101) (PDF p. 31)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Release
import Definitions.Def_HigherOrderId_Certify_Fisher
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion

open Matrix

namespace HigherOrderId.Certify

/-- §C.2, Eq. (101) (covariance Frobenius bounds). There are universal constants `c_0, C_0 > 0`
such that, with `v_N = σ²(d − m)/(Nα²)`: for every design in `𝔇_{d,m}(α)` whose full
value–gradient Fisher information is positive definite (full rank), the efficient covariance
satisfies `‖Σ^eff_m‖_F ≥ c_0 v_N √(d² + m⁶)` (coordinates (99)); and the explicit completion
estimator of Appendix B (full span when `m = 0`; the weighted frame `U_w`, `w = m^{1/4}`, when
`m ≥ 1`), together with the estimator of `b`, has covariance `Γ_m` with
`‖Γ_m‖_F ≤ C_0 v_N √(d² + m⁶)`. -/
theorem eq_101 :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      (∀ (d m N : ℕ) (α σ : ℝ) (D : Design d (d - m + 1)), 10 ≤ d → m ≤ md d → 0 < α →
        α ≤ 1 / 2 → 0 < σ → InDesignClass d m N α D → (fullFisherMat D σ).PosDef →
        c₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6) ≤ frobNorm (SigmaEff D σ)) ∧
      (∀ (d m N : ℕ) (α σ : ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
          (V : Matrix (Fin d) (Fin (d - m)) ℝ), 10 ≤ d → m ≤ md d → 0 < α → α ≤ 1 / 2 →
        0 < σ → (d - m + 1) ∣ N → 0 < N / (d - m + 1) →
        Uᵀ * U = 1 → Vᵀ * V = 1 → Uᵀ * V = 0 →
        (1 ≤ m → ∃ ι : FrameRows m ↪ Fin d, U = Uw ι ((m : ℝ) ^ ((1 : ℝ) / 4))) →
        frobNorm (GammaTheta U V σ N (vN d m N α σ)) ≤
          C₀ * vN d m N α σ * Real.sqrt ((d : ℝ) ^ 2 + (m : ℝ) ^ 6)) := by sorry

end HigherOrderId.Certify
