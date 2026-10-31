-- Prove2me | Theorems.Thm_OneStepProx_corollary_2_2
-- name    : OneStepProx.corollary_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:55.582984+00:00
-- url     : https://prove2.me/theorems/db52201b-458b-4c6c-a3fe-79c54690f1c5
-- title:
--   Corollary 2.2, p.9 — the conclusion of Theorem 2.1 for approximate fixed points (2.4)
-- statement:
--   Let the setting be that of Theorem 2.1: on a probability space $(\Omega,\mathcal A,P)$, random functions $g_n$ on an open $\Theta\subseteq\mathbb R^d$ that are continuously differentiable with probability 1, random functions $h_n:\mathbb R^d\to\mathbb R\cup\{\infty\}$ that are convex and proper with probability 1 and finite only inside $\Theta$, a positive definite matrix $H$ and random matrices $C_n$ such that
--
--   1. for each $M>0$, $\sup_{\sqrt n\|\theta-\hat\theta\|<M}\|\sqrt n(\nabla g_n(\theta)-\nabla g_n(\hat\theta))-\sqrt nH(\theta-\hat\theta)\|\xrightarrow{P}0$, and
--   2. $C_n\succ0$ and $C_n^{-1}H\xrightarrow{P}I$.
--
--   Suppose $\hat\theta=\hat\theta_n$ is **not necessarily a minimizer** of $g_n+h_n$, but is an approximate fixed point of scaled proximal gradient descent:
--
--   $$
--   \sqrt n\,\Bigl\|\operatorname{prox}^{C_n}_{h_n}\bigl(\hat\theta-C_n^{-1}\nabla g_n(\hat\theta)\bigr)-\hat\theta\Bigr\|=o_P(1). \tag{2.4}
--   $$
--
--   Then for any $\sqrt n$-consistent estimator $\hat\theta_{init}$ of $\hat\theta$, the one-step estimator $\hat\theta_{ose}$ of (2.2) satisfies
--
--   $$
--   \sqrt n\,\|\hat\theta_{ose}-\hat\theta\|\xrightarrow{P}0 .
--   $$
--
--   This extends the conclusion of Theorem 2.1 to stationary points, because $g_n$ need not be convex.
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
--   - reading: $\hat\theta$ "not necessarily a minimizer\" → $\hat\theta\in\Theta$ almost surely, for each $n$; reason: (i) and (2.4) evaluate $\nabla g_n(\hat\theta)$, which exists only on $\Theta$; for a minimizer this follows from $\hat\theta\in D_n\subseteq\Theta$.
--   - encoding: (2.4) $\sqrt n\|\operatorname{prox}(\hat\theta-C_n^{-1}\nabla g_n(\hat\theta))-\hat\theta\|=o_P(1)$ → a given sequence $\hat\theta_{fix}$ in that prox almost surely with $\sqrt n\|\hat\theta_{fix}-\hat\theta\|\xrightarrow{P}0$; reason: the prox is a set with at most one point for $C_n\succ0$, so the selection is immaterial.
--   - generalization: random objects → plain functions of $\omega$, no measurability assumed; reason: probabilities are outer measures, which agree with $P$ on measurable events, so the measurable case is included.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, Corollary 2.2, p.9, with (2.4), p.8

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx
import Definitions.Def_OneStepProx_IsLocallyLinearized

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

namespace OneStepProx

/-- Corollary 2.2 (Bassett & Deride, arXiv:2004.14521v3, p.9): in the setting of Theorem 2.1, if
`θ̂` satisfies (2.4), p.8, `√n ‖prox^{Cₙ}_{hₙ}(θ̂ − Cₙ⁻¹∇gₙ(θ̂)) − θ̂‖ = o_P(1)`, then the conclusion
of Theorem 2.1 holds even if `θ̂` is not necessarily a minimizer of `gₙ + hₙ`.

**Formalization Note.** See `theorem_2_1` for the encoding. `θfix` is a selection of the prox in
(2.4); the prox is single-valued for `C ≻ 0`, so the selection is immaterial. In place of
minimality, `θhat n ω ∈ Θ` almost surely is assumed, as the gradient at `θ̂` is taken in `Θ`. -/
theorem corollary_2_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsOpen Θ)
    (g : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ) (D : ℕ → Ω → Set (EuclideanSpace ℝ (Fin d)))
    (h : ℕ → Ω → EuclideanSpace ℝ (Fin d) → ℝ) (C : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (θhat θinit θose θfix : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hg : ∀ n, ∀ᵐ ω ∂P, ContDiffOn ℝ 1 (g n ω) Θ)
    (hh : ∀ n, ∀ᵐ ω ∂P, D n ω ⊆ Θ ∧ IsProperConvex (D n ω) (h n ω))
    (hθhat : ∀ n, ∀ᵐ ω ∂P, θhat n ω ∈ Θ)
    (hfix : ∀ n, ∀ᵐ ω ∂P, θfix n ω ∈ scaledProx (C n ω) (D n ω) (h n ω)
      (θhat n ω - Matrix.toEuclideanLin (C n ω)⁻¹ (gradient (g n ω) (θhat n ω))))
    (h24 : TendstoInMeasure P (fun (n : ℕ) ω => Real.sqrt n * ‖θfix n ω - θhat n ω‖) atTop (fun _ => 0))
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
