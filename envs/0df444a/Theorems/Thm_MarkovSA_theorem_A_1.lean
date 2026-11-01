-- Prove2me | Theorems.Thm_MarkovSA_theorem_A_1
-- name    : MarkovSA.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:30.738145+00:00
-- url     : https://prove2.me/theorems/7bdfff9d-f961-4677-a769-981722e0cd29
-- title:
--   Theorem A.1 — product-sum bound under Condition A.1 (corrected: $t_k\ge1$)
-- statement:
--   Throughout, $E$ is a finite-dimensional real space with the contraction norm $\|\cdot\|_c$, $(x_k)$ are the iterates of Algorithm (6) run with positive stepsizes $(\alpha_k)$ satisfying Condition A.1, Assumptions 2.1–2.4 hold (the chain being Markov relative to a filtration to which the iterates are adapted), $(\|\cdot\|_s,L,\ell_{cs},u_{cs},\theta)$ are admissible smoothing data, $M$ is the generalized Moreau envelope, $u_{cm}^2=1+\theta u_{cs}^2$, $\ell_{cm}^2=1+\theta\ell_{cs}^2$, $A=A_1+A_2+1$, $B=B_1+B_2$, and $t_k=t_{\alpha_k}$.
--
--   **Theorem A.1.** Let $K$ be the least $K_0$ with $t_k\le k$ for every $k\ge K_0$ (assumed to exist), and assume $t_k\ge1$ for every $k\ge K$. Then, with $c_1=(\|x_0-x^*\|_c+\|x_0\|_c+B/A)^2$ and $c_2=(A\|x^*\|_c+B)^2$:
--
--   1. for any $k\in[0,K-1]$, $\|x_k-x^*\|_c^2\le c_1$ almost surely;
--   2. for any $k\ge K$,
--   $$
--   \mathbb E\big[\|x_k-x^*\|_c^2\big]\le\varphi_1c_1\prod_{j=K}^{k-1}(1-\varphi_2\alpha_j)+\varphi_3c_2\sum_{i=K}^{k-1}\alpha_i\alpha_{i-t_i,i-1}\prod_{j=i+1}^{k-1}(1-\varphi_2\alpha_j).
--   $$
--
--   It is the general finite-sample bound from which every case of Theorem 2.1 is evaluated.
--
--   Differences from the source:
--   - reading: $\{Y_k\}$ is a Markov chain and $\{w_k\}$ a random process; their joint law is not stated → $Y$ is Markov with matrix $P$ relative to a filtration $\mathcal G$ to which $Y$ and the iterates are adapted; reason: the proof (p.34) conditions the chain on past iterates; with $w\equiv0$ the natural filtration of $Y$ qualifies
--   - reading: initial estimate $x_0$ → a fixed vector $x_0$; the law of $Y_0$ is arbitrary; reason: $c_1$ contains $\|x_0\|_c$ and part (1) bounds $\|x_k-x^*\|_c^2$ a.s. by a constant
--   - encoding: unique stationary distribution $\mu$ → $\mu$ stationary; uniqueness not assumed; reason: uniqueness follows from the geometric decay of Assumption 2.3
--   - encoding: $\mathbb R^d$ with an arbitrary norm $\|\cdot\|_c$ → a finite-dimensional real normed space $E$ with its norm; reason: the same spaces up to linear isometry; $d$ does not appear in the statement
--   - reading: $\|\cdot\|_s$, $\ell_{cs}$, $u_{cs}$, $\theta$ 'properly chosen' → any smoothing data meeting the conditions of p.24; reason: the paper fixes one such choice without specifying it; the claim holds for each
--   - generalization: $\|w_k\|_c\le A_2\|x_k\|_c+B_2$ (no qualifier) → the same bound almost surely; reason: a pathwise bound implies the almost-sure one, so the statement specializes to the source's
--   - encoding: $\{w_k\}$ a random process → each $w_k$ measurable; reason: needed for $\mathbb E[w_k\mid\mathcal F_k]$ to be defined; it excludes only undefined cases
--   - reading: a stepsize sequence $\{\alpha_k\}$ (Condition A.1 states no sign) → $\alpha_k>0$ for every $k$; reason: stepsizes are positive throughout the paper ($\alpha/(k+h)^\xi$ with $\alpha,h>0$)
--   - encoding: $\alpha_{i,j}=\sum_{k=i}^{j}\alpha_k$ → window sum over $[i,j)$, so $\alpha_{k-t_k,k-1}$ is the sum over $[k-t_k,k)$; reason: avoids natural-number subtraction; same values, and the empty sum when $t_k=0$
--   - reading: $K=\min\{k\ge0:k\ge t_k\}$, then used as if $t_k\le k$ for all $k\ge K$ → $K$ = least $K_0$ with $t_k\le k$ for every $k\ge K_0$, and such a $K_0$ is assumed to exist; reason: with the printed $K$ the right side can contain a negative index (two-state chain whose stepsize drops by a factor 8 after step $m$); the proof uses the read $K$
--   - correction: for all $k\ge t_k$, with $t_k\ge0$ → the hypothesis $t_k\ge1$ for every $k\ge K$; reason: the proof bounds $\alpha_k$ (or $\alpha_k^2$) by $\alpha_k\alpha_{k-t_k,k-1}$, false for an empty window; counterexample: on $\mathcal Y=\{-1,1\}$ let $P=\frac12U+\frac12I$ ($U$ the uniform matrix), $\mu$ uniform, $C=\sigma=\frac12$, $F(x,y)=y$, $w\equiv0$, $x_0=0$, $Y_0$ uniform, $E=\mathbb R$, $\|\cdot\|_s=|\cdot|$, $L=\ell_{cs}=u_{cs}=\theta=1$, $\beta=\frac12$, $\alpha_k\equiv0.6$; then $t_k=0$ for all $k$ and Condition A.1 holds vacuously, $M(x)=x^2/4$; $K=0$ and at $k=1$, $\mathbb E[x_1^2]=0.36$ while the right side is $\varphi_1c_1(1-0.6\varphi_2)=\frac49\cdot0.7\approx0.31$
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Theorem A.1, p.24

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_MarkovSA_Fbar
import Definitions.Def_MarkovSA_saIter
import Definitions.Def_MarkovSA_sigmaF
import Definitions.Def_MarkovSA_IsMarkovWrt
import Definitions.Def_MarkovSA_Assumption21
import Definitions.Def_MarkovSA_Assumption22
import Definitions.Def_MarkovSA_Assumption23
import Definitions.Def_MarkovSA_Assumption24
import Definitions.Def_MarkovSA_IsSAInstance
import Definitions.Def_MarkovSA_IsNormFun
import Definitions.Def_MarkovSA_IsSmoothNorm
import Definitions.Def_MarkovSA_IsSmoothingData
import Definitions.Def_MarkovSA_phi1
import Definitions.Def_MarkovSA_phi2
import Definitions.Def_MarkovSA_phi3
import Definitions.Def_MarkovSA_Aconst
import Definitions.Def_MarkovSA_Bconst
import Definitions.Def_MarkovSA_c1
import Definitions.Def_MarkovSA_c2
import Definitions.Def_MarkovSA_stepMix
import Definitions.Def_MarkovSA_winSum
import Definitions.Def_MarkovSA_Kidx
import Definitions.Def_MarkovSA_ConditionA1
import Definitions.Def_MarkovSA_polyStep
import Definitions.Def_MarkovSA_Admissible
import Definitions.Def_MarkovSA_moreauM
open MeasureTheory

namespace MarkovSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Theorem A.1** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, Appendix A, p.24), corrected by `t_k ≥ 1` (C1), with `K` read by R2.
Under Assumptions 2.1–2.4 and Condition A.1:
(1) for any `k ∈ [0, K − 1]`, `‖x_k − x*‖_c² ≤ c₁` almost surely;
(2) for any `k ≥ K`, `E[‖x_k − x*‖_c²] ≤ φ₁c₁ ∏_{j=K}^{k−1}(1 − φ₂α_j) + φ₃c₂ Σ_{i=K}^{k−1} α_iα_{i−t_i,i−1} ∏_{j=i+1}^{k−1}(1 − φ₂α_j)`,
where `c₁ = (‖x₀ − x*‖_c + ‖x₀‖_c + B/A)²` and `c₂ = (A‖x*‖_c + B)²`.

The standing hypotheses are those of Theorem A.1 (p.24): Assumptions 2.1–2.4 (`IsSAInstance`, `Assumption23`),
the smoothing data of p.24 (`IsSmoothingData`), and Condition A.1 for the positive stepsizes `α`.

**Formalization Note.** `K = Kidx t` is the least `K₀` with `t_k ≤ k` for all `k ≥ K₀` (reading R2); such a
`K₀` is assumed to exist. `t_k ≥ 1` for every `k ≥ K` is the correction C1; it forces `K ≥ 1`. -/
theorem theorem_A_1 (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) (hchain : Assumption23 P μ C σ)
    (β A₁ B₁ A₂ B₂ : ℝ) (s : E → ℝ) (L ℓ u θ : ℝ) (hsm : IsSmoothingData s L ℓ u θ β)
    (α : ℕ → ℝ) (hpos : ∀ k, 0 < α k)
    (hA1 : ConditionA1 (stepMix P μ α) α (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂))
    (F : E → 𝒴 → E) (x₀ xstar : E) (Y : ℕ → Ω → 𝒴) (G : Filtration ℕ mΩ) (w : ℕ → Ω → E)
    (hinst : IsSAInstance Pr P μ β A₁ B₁ A₂ B₂ α F x₀ xstar Y G w)
    (ht1 : ∀ k, Kidx (stepMix P μ α) ≤ k → 1 ≤ stepMix P μ α k)
    (hK : ∃ K₀ : ℕ, ∀ k, K₀ ≤ k → stepMix P μ α k ≤ k) :
    (∀ k : ℕ, k < Kidx (stepMix P μ α) →
      ∀ᵐ ω ∂Pr, ‖saIter F α x₀ Y w k ω - xstar‖ ^ 2 ≤ c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂)) ∧
    ∀ k : ℕ, Kidx (stepMix P μ α) ≤ k →
      ∫ ω, ‖saIter F α x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
        phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) *
            ∏ j ∈ Finset.Ico (Kidx (stepMix P μ α)) k, (1 - phi2 β ℓ u θ * α j) +
          phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) *
            ∑ i ∈ Finset.Ico (Kidx (stepMix P μ α)) k,
              α i * winSum α (i - stepMix P μ α i) i * ∏ j ∈ Finset.Ico (i + 1) k, (1 - phi2 β ℓ u θ * α j) := by sorry

end MarkovSA
