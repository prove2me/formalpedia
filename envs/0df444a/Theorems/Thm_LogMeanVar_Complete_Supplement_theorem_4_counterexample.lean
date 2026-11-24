-- Prove2me | Theorems.Thm_LogMeanVar_Complete_Supplement_theorem_4_counterexample
-- name    : LogMeanVar.Complete.Supplement.theorem_4_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:02:36.264466+00:00
-- url     : https://prove2.me/theorems/210f36e5-d9fd-485a-8697-e58c2974f688
-- title:
--   Theorem 4 (corrected: counterexample to the unconditional Markov representation claim)
-- statement:
--   The Markov conclusion of Theorem 4(ii) does not follow from the stated state-SDE assumptions. Let $B^X$ be Brownian, let $\tau$ be its first hit of one, and set $X_t=(t-\tau)_+^2$. Take one stock and one state, $T=2$, $\sigma=\gamma=1$, $\rho=0$, $\mu=r=x$, $m=2\sqrt{x}$, $\nu=0$ and deterministic constraints $\Pi=\{0\}$. An independent stock Brownian motion is included. This is a permitted scalar instance of the arbitrary-dimensional theorem.
--
--   The state solves $dX_t=2\sqrt{X_t}\,dt$, and $0\le X_t\le4$ on the horizon. The unique allowed portfolio is zero, $\theta=0$, and the formal conclusion checks that the deterministic constraint is closed and convex and contains zero, that the zero portfolio minimizes the exact scalar objective from (45), and that its allocation drift equals the BSDE driver $g(t,z)=X_t$. The BSDE has a unique classical solution, with
--
--   $$Y_t=\mathbb E_t\!\left[\int_0^2X_s\,ds\right]-\int_0^tX_s\,ds.$$
--
--   It satisfies the proof’s right-continuous-$Z$, square-integrable-driver and true-martingale requirements. Nevertheless,
--
--   $$\nexists f:\mathbb R\times\mathbb R\to\mathbb R\quad\text{such that}\quad Y_1=f(1,X_1)\text{ almost surely}.$$
--
--   On the positive-probability event that the hit has not occurred by time one, $X_1=0$, while $Y_1$ varies strictly with the observed Brownian position. Uniqueness of the BSDE does not repair nonuniqueness and non-Markov behavior of the state equation. The verification and return identities in part (i) are not refuted. DISPROOF.md records the construction and the additional Markov-state premise a corrected part (ii) would require.
--
--   Differences from the source:
--   - correction: deterministic state-dependent constraints and BSDE uniqueness imply Y_t=f(t,X_t) for a state specified only by (5)/(35) → a scalar countermodel satisfying the coefficient assumptions, deterministic constraints and unique classical BSDE, with no such representing function even at t=1; reason: the nonunique state ODE permits a Brownian-triggered waiting solution; its current state omits information about the remaining waiting time
--   - encoding: the vector theorem includes all positive finite stock/state dimensions and the proof’s classical-solution conventions → N=K=1 counterexample, including a stock Brownian motion, actual return equation and a unique BSDE with right-continuous Z, L² driver and true martingale; reason: one permitted instance disproves the full statement; no finite-reward or solution-class pathology is used
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. O–11–O–13, Theorem 4(ii), (46); p. 8, state equation (5)

import Definitions.Def_LogMeanVar_Complete_Supplement_Countermodels

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace LogMeanVar.Complete.Supplement

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), pp.O–11–O–13, Theorem 4
(corrected: counterexample to the Markov conclusion under the printed SDE assumptions).
Take N=K=1, Π={0}, μ=r=x, σ=γ=1, ν=0, m=2√x and T=2. The state waits at zero
until B^X hits 1 and then follows (t-τ)². The constrained generator (45) is X_t.
There is a unique classical BSDE solution, including all the proof's extra
right-continuity, L²-driver and true-martingale conventions, yet no function of
(t,X_t) represents its Y even at t=1.
Formalization Note: the source imposes only right continuity of coefficients, not
uniqueness/Markov transition laws for the state SDE. This example satisfies even
continuity of the coefficients. It refutes part (ii), not the verification and
return identities of part (i). An independent stock Brownian motion B is included (ρ=0); its integral is
zero because Π={0}. The joint filtration is used for the return equation,
and the state Brownian filtration for the BSDE, as in the source. -/
theorem theorem_4_counterexample {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B W : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (hBmeas : ∀ t, StronglyMeasurable (B t))
    (hBW : IndepFun (fun ω => fun t => B t ω) (fun ω => fun t => W t ω) P)
    (hW : IsBrownianReal W P) (hWmeas : ∀ t, StronglyMeasurable (W t))
    (hWcont : ∀ ω, Continuous (fun u => W u ω)) :
    let F := Filtration.natural W hWmeas
    let G := Filtration.natural (fun t ω => (B t ω, W t ω))
      (fun t => (hBmeas t).prodMk (hWmeas t))
    CorrelatedNoise P G B W 0 ∧
    IsReturn waitingModel P G B (waitingState W) (fun _ _ _ => 0)
      0 (fun _ => 0) (waitingReturn W) ∧
    MemLp (waitingReturn W 2) 2 P ∧
    PrintedAdmissible waitingModel P G (waitingState W) (waitingReturn W) (fun _ _ _ => 0) 0 ∧
    waitingModel.Standing ∧
    waitingModel.AdaptedAlong G (waitingState W) ∧
    IsState waitingModel P F W (waitingState W) ∧
    (∀ t x : ℝ, IsClosed (waitingConstraints t x) ∧
      Convex ℝ (waitingConstraints t x) ∧ (0 : ℝ) ∈ waitingConstraints t x) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ ω, ∀ z : ℝ,
      waitingPortfolio t z ∈ waitingConstraints t (waitingState W t ω) ∧
      (∀ p ∈ waitingConstraints t (waitingState W t ω),
        allocationObjective waitingModel 1 0 t (waitingState W t ω) z
          (waitingPortfolio t z) ≤
        allocationObjective waitingModel 1 0 t (waitingState W t ω) z p) ∧
      waitingDriver W t ω z =
        allocationDrift waitingModel t (waitingState W t ω) (waitingPortfolio t z)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ ω, waitingState W t ω ∈ Set.Icc (0 : ℝ) 4) ∧
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 2,
      ENNReal.ofReal (((waitingModel.μ s (waitingState W s ω) -
        waitingModel.r s (waitingState W s ω)) / waitingModel.σ s (waitingState W s ω)) ^ 2)
      ∂volume ∂P) = 0 ∧
    ∃ Y Z : ℝ → Ω → ℝ,
      ClassicalBSDE P F W 2 (waitingDriver W) Y Z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ᵐ ω ∂P, Y t ω = waitingValue P F W t ω) ∧
      (∀ Y' Z' : ℝ → Ω → ℝ, ClassicalBSDE P F W 2 (waitingDriver W) Y' Z' →
        SameSolution P 2 Y Z Y' Z') ∧
      ¬∃ f : ℝ → ℝ → ℝ, ∀ᵐ ω ∂P, Y 1 ω = f 1 (waitingState W 1 ω) := by sorry

end LogMeanVar.Complete.Supplement
