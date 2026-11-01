-- Prove2me | Theorems.Thm_MarkovSA_lemma_A_2
-- name    : MarkovSA.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:26.390213+00:00
-- url     : https://prove2.me/theorems/dfab7dc0-4489-4994-9fdd-4443966e67c3
-- title:
--   Lemma A.2 — iterate displacement over a short window
-- statement:
--   Throughout, $E$ is a finite-dimensional real space with the contraction norm $\|\cdot\|_c$, $(x_k)$ are the iterates of Algorithm (6) run with positive stepsizes $(\alpha_k)$ satisfying Condition A.1, Assumptions 2.1–2.4 hold (the chain being Markov relative to a filtration to which the iterates are adapted), $(\|\cdot\|_s,L,\ell_{cs},u_{cs},\theta)$ are admissible smoothing data, $M$ is the generalized Moreau envelope, $u_{cm}^2=1+\theta u_{cs}^2$, $\ell_{cm}^2=1+\theta\ell_{cs}^2$, $A=A_1+A_2+1$, $B=B_1+B_2$, and $t_k=t_{\alpha_k}$.
--
--   **Lemma A.2.** Let $k_1\le k_2$ be nonnegative integers with $\alpha_{k_1,k_2-1}\le\frac1{4A}$. Then almost surely, for all $k\in[k_1,k_2]$,
--
--   $$
--   \|x_k-x_{k_1}\|_c\le2\alpha_{k_1,k_2-1}\big(A\|x_{k_1}\|_c+B\big)\quad\text{and}\quad\|x_k-x_{k_1}\|_c\le4\alpha_{k_1,k_2-1}\big(A\|x_{k_2}\|_c+B\big).
--   $$
--
--   It controls how far the iterates move over a window of total stepsize at most $1/(4A)$.
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
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Lemma A.2, p.26

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

/-- **Lemma A.2** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §A.1.2, p.26). Given non-negative integers `k₁ ≤ k₂` with `α_{k₁,k₂−1} ≤ 1/(4A)`,
for all `k ∈ [k₁, k₂]`: `‖x_k − x_{k₁}‖_c ≤ 2α_{k₁,k₂−1}(A‖x_{k₁}‖_c + B)` and
`‖x_k − x_{k₁}‖_c ≤ 4α_{k₁,k₂−1}(A‖x_{k₂}‖_c + B)`.

The standing hypotheses are those of Theorem A.1 (p.24): Assumptions 2.1–2.4 (`IsSAInstance`, `Assumption23`),
the smoothing data of p.24 (`IsSmoothingData`), and Condition A.1 for the positive stepsizes `α`. `winSum α k₁ k₂` is `α_{k₁,k₂−1}`. The bounds hold almost surely (Assumption 2.4 (2) is almost sure). -/
theorem lemma_A_2 (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) (hchain : Assumption23 P μ C σ)
    (β A₁ B₁ A₂ B₂ : ℝ) (s : E → ℝ) (L ℓ u θ : ℝ) (hsm : IsSmoothingData s L ℓ u θ β)
    (α : ℕ → ℝ) (hpos : ∀ k, 0 < α k)
    (hA1 : ConditionA1 (stepMix P μ α) α (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂))
    (F : E → 𝒴 → E) (x₀ xstar : E) (Y : ℕ → Ω → 𝒴) (G : Filtration ℕ mΩ) (w : ℕ → Ω → E)
    (hinst : IsSAInstance Pr P μ β A₁ B₁ A₂ B₂ α F x₀ xstar Y G w)
    (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) (hwin : winSum α k₁ k₂ ≤ 1 / (4 * Aconst A₁ A₂)) :
    ∀ᵐ ω ∂Pr, ∀ k ∈ Finset.Icc k₁ k₂,
      ‖saIter F α x₀ Y w k ω - saIter F α x₀ Y w k₁ ω‖ ≤ 2 * winSum α k₁ k₂ * (Aconst A₁ A₂ * ‖saIter F α x₀ Y w k₁ ω‖ + Bconst B₁ B₂) ∧
      ‖saIter F α x₀ Y w k ω - saIter F α x₀ Y w k₁ ω‖ ≤ 4 * winSum α k₁ k₂ * (Aconst A₁ A₂ * ‖saIter F α x₀ Y w k₂ ω‖ + Bconst B₁ B₂) := by sorry

end MarkovSA
