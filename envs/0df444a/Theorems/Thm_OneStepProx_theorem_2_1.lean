-- Prove2me | Theorems.Thm_OneStepProx_theorem_2_1
-- name    : OneStepProx.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:04.654263+00:00
-- url     : https://prove2.me/theorems/1b74a723-d6f6-49b1-8235-f94d55ff4618
-- title:
--   Theorem 2.1, p.6 — one scaled proximal gradient step from a $\sqrt n$-consistent start is asymptotically equivalent to the composite-model estimator
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $\Theta\subseteq\mathbb R^d$ open. Let $g_n$ and $h_n$ be random functions with values in $\mathbb R$ and $\mathbb R\cup\{\infty\}$, and let $C_n$ be random $d\times d$ matrices. Suppose that with probability 1, $g_n$ is continuously differentiable on $\Theta$ and $h_n$ is convex and proper and finite only inside $\Theta$. Let $\hat\theta=\hat\theta_n$ be a minimizer of the composite model,
--
--   $$
--   \hat\theta=\operatorname*{argmin}_{\theta\in\Theta}\ g_n+h_n, \tag{2.1}
--   $$
--
--   which is assumed to exist almost surely. Assume that $H$ is a positive definite matrix such that
--
--   1. for each $M>0$,
--      $$
--      \sup_{\sqrt n\|\theta-\hat\theta\|<M}\Bigl\|\sqrt n\bigl(\nabla g_n(\theta)-\nabla g_n(\hat\theta)\bigr)-\sqrt n\,H(\theta-\hat\theta)\Bigr\|\xrightarrow{P}0;
--      $$
--   2. $C_n\succ0$ and $C_n^{-1}H\xrightarrow{P}I$, where $I$ is the $d\times d$ identity matrix.
--
--   Then for any estimator $\hat\theta_{init}$ with $\sqrt n(\hat\theta_{init}-\hat\theta)=O_P(1)$, and any one-step estimator
--
--   $$
--   \hat\theta_{ose}=\operatorname{prox}^{C_n}_{h_n}\bigl(\hat\theta_{init}-C_n^{-1}\nabla g_n(\hat\theta_{init})\bigr), \tag{2.2}
--   $$
--
--   assumed to exist almost surely, the estimators $\hat\theta$ and $\hat\theta_{ose}$ are asymptotically equivalent:
--
--   $$
--   \sqrt n\,\|\hat\theta_{ose}-\hat\theta\|\xrightarrow{P}0 .
--   $$
--
--   This is the proximal analogue of the classical result that one Newton–Raphson step from a $\sqrt n$-consistent start is asymptotically equivalent to the maximum likelihood estimator. It says that the numerical tolerance of a scaled proximal gradient method need only scale like $n^{-1/2}$.
--
--   **Formalization Note** $h_n$ is encoded by its effective domain and its finite values. The proximal operator is a set, so (2.2) is a membership. No measurability is assumed: the probability of an event is its outer measure. Matrix convergence is in the spectral norm.
--
--   Differences from the source:
--   - reading: "asymptotically equivalent", which p.2 words as $\sqrt n$-consistency, $O_P(1)$ → $\sqrt n\|\hat\theta_{ose}-\hat\theta\|\xrightarrow{P}0$; reason: the proof, p.7, states and proves $o_P(1)$; this is the stronger of the two readings.
--   - reading: the sup of the vector $\sqrt n(\nabla g_n(\theta)-\nabla g_n(\hat\theta))-\sqrt nH(\theta-\hat\theta)$ in (i), printed without a norm → the sup of its Euclidean norm, written as: the probability that some $\theta\in\Theta$ in the ball has norm $>\varepsilon$ tends to $0$; reason: a sup of vectors has no meaning; that event is exactly $\{\sup>\varepsilon\}$.
--   - reading: (i) "for each $M>0$, there is a positive definite matrix $H$", with (ii) using $H$ → one positive definite $H$ for all $M$ and for (ii); reason: (ii) uses a single $H$ and determines it, since $C_n^{-1}H\to I$ and $C_n^{-1}H'\to I$ force $H=H'$.
--   - reading: $g_n,h_n$ on $\Theta\subseteq\mathbb R^d$ with $h_n$ valued in $\mathbb R\cup\{\infty\}$ and a prox over $w\in\mathbb R^d$ → an open $\Theta$, with the effective domain of $h_n$ inside $\Theta$, so that $h_n=+\infty$ off $\Theta$; reason: $\nabla g_n$ on $\Theta$ needs an open set (§1.1, p.2, takes $\Theta$ open), the prox over $\mathbb R^d$ needs $h_n$ on all of $\mathbb R^d$; $\Theta=\mathbb R^d$ is included.
--   - reading: $\hat\theta_{init}$ an estimator, with $\nabla g_n(\hat\theta_{init})$ evaluated in (2.2) → $\hat\theta_{init}\in\Theta$ almost surely, for each $n$; reason: $\nabla g_n$ exists only on $\Theta$.
--   - reading: "$C_n\succ0$" in (ii) → $C_n\succ0$ almost surely, for each $n$; reason: the setting is almost sure, and this is the weaker hypothesis.
--   - encoding: $\succ0$ → `Matrix.PosDef`; reason: it includes symmetry, as the scaled norm and the eigenvalues presuppose.
--   - encoding: $h_n$ extended-valued → an effective domain $D_n$ and finite values on it; reason: every proper convex function has this form.
--   - encoding: "with probability 1", "$P$-almost surely\" → for each $n$, $\forall^{a.e.}\omega$; reason: $\mathbb N$ is countable, so this is the same as almost surely for all $n$.
--   - encoding: $\sqrt n(\hat\theta_{init}-\hat\theta)=O_P(1)$ → `ResidualsDRO.Unified.IsBigOp` with rate $1$: for $\delta>0$ there are $M>0$, $N$ with $P(\sqrt n\|\hat\theta_{init}-\hat\theta\|>M)\le\delta$ for $n\ge N$; reason: boundedness in probability, eventually in $n$, which is implied by the bound for all $n$.
--   - encoding: $C_n^{-1}H\xrightarrow{P}I$ → convergence in measure in the spectral norm; reason: all matrix norms give the same convergence.
--   - encoding: (2.2) "$\hat\theta_{ose}=\operatorname{prox}\dots$", "assumed to exist $P$-almost surely\" → a given sequence with $\hat\theta_{ose}\in\operatorname{prox}\dots$ almost surely; reason: the prox is a set; existence is the paper's assumption.
--   - encoding: (2.1) "$\hat\theta=\operatorname{argmin}$", "assumed to exist $P$-almost surely\" → a given sequence with $\hat\theta\in D_n$ minimizing $g_n+h_n$ over $D_n$ almost surely; reason: the value is $+\infty$ off $D_n$, and $D_n$ is nonempty.
--   - generalization: random objects → plain functions of $\omega$, no measurability assumed; reason: probabilities are outer measures, which agree with $P$ on measurable events, so the measurable case is included.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, Theorem 2.1, p.6, with (2.1), (2.2), p.6, and the proof, pp.6–8

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx
import Definitions.Def_OneStepProx_IsLocallyLinearized

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

namespace OneStepProx

/-- Theorem 2.1 (Bassett & Deride, One-Step Estimation with Scaled Proximal Methods,
arXiv:2004.14521v3, p.6). Let `θ̂` be a minimizer (2.1) of `gₙ + hₙ`, where with probability 1 `gₙ`
is continuously differentiable and `hₙ` is convex and proper. Assume (i) the local linearization
of `∇gₙ` at `θ̂` with a positive definite `H` and (ii) `Cₙ ≻ 0`, `Cₙ⁻¹H →ᴾ I`. Then for any
`√n`-consistent estimator `θ̂init` of `θ̂`, the one-step estimator `θ̂ose` of (2.2) satisfies
`√n‖θ̂ose − θ̂‖ →ᴾ 0`.

**Formalization Note.**
* `ℝ^d` is `EuclideanSpace ℝ (Fin d)`; `Θ` is an open subset (`Θ = Set.univ` is the case of
  functions on all of `ℝ^d`). The values of `gₙ` off `Θ` are never read.
* `hₙ : ℝ^d → ℝ ∪ {∞}` is encoded by its effective domain `D n ω ⊆ Θ` and its finite values
  `h n ω` on it (`IsProperConvex`); it is `+∞` off `D n ω`, so a minimizer lies in `D n ω` and it
  suffices to compare with the points of `D n ω`.
* "`C ≻ 0`" is `Matrix.PosDef`, which includes symmetry; `(C n ω)⁻¹` is the matrix inverse.
* `P`-almost surely is `∀ᵐ ω ∂P`, for each `n`. Random objects are plain functions with no
  measurability assumed; probabilities of events that need not be measurable are outer measures.
* Convergence in probability is `TendstoInMeasure`, for matrices in the spectral norm
  (`Matrix.Norms.L2Operator`). `O_P(1)` is `ResidualsDRO.Unified.IsBigOp … (fun _ => 1)`.
* `(2.1)` and `(2.2)` assume existence: `θhat` and `θose` are given sequences satisfying them
  almost surely, the prox being a set (`scaledProx`).
* Asymptotic equivalence is the proof's `√n‖θ̂ose − θ̂‖ = o_P(1)`. -/
theorem theorem_2_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsOpen Θ)
    (g : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ) (D : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (h : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ) (C : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (θhat θinit θose : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hg : ∀ n, ∀ᵐ ω ∂P, ContDiffOn ℝ 1 (g n ω) Θ)
    (hh : ∀ n, ∀ᵐ ω ∂P, D n ω ⊆ Θ ∧ IsProperConvex (D n ω) (h n ω))
    (hθhat : ∀ n, ∀ᵐ ω ∂P, θhat n ω ∈ D n ω ∧
      ∀ θ ∈ D n ω, g n ω (θhat n ω) + h n ω (θhat n ω) ≤ g n ω θ + h n ω θ)
    (hH : H.PosDef) (hi : IsLocallyLinearized P Θ g θhat H)
    (hC : ∀ n, ∀ᵐ ω ∂P, (C n ω).PosDef)
    (hii : TendstoInMeasure P (fun n ω => (C n ω)⁻¹ * H) atTop (fun _ => 1))
    (hinitΘ : ∀ n, ∀ᵐ ω ∂P, θinit n ω ∈ Θ)
    (hinit : ResidualsDRO.Unified.IsBigOp P
      (fun (n : ℕ) ω => ENNReal.ofReal (Real.sqrt n * ‖θinit n ω - θhat n ω‖)) (fun _ => 1))
    (hose : ∀ n, ∀ᵐ ω ∂P, θose n ω ∈ scaledProx (C n ω) (D n ω) (h n ω)
      (θinit n ω - Matrix.toEuclideanLin (C n ω)⁻¹ (gradient (g n ω) (θinit n ω)))) :
    TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n * ‖θose n ω - θhat n ω‖) atTop (fun _ => 0) := by sorry

end OneStepProx
