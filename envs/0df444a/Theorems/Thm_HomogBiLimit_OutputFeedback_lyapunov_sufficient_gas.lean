-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_lyapunov_sufficient_gas
-- name    : HomogBiLimit.OutputFeedback.lyapunov_sufficient_gas
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T10:26:09.206994+00:00
-- url     : https://prove2.me/theorems/a38b413d-020e-400c-aeb1-52dddf3e1f39
-- title:
--   Lyapunov's direct method: a strict proper Lyapunov function gives global asymptotic stability (continuous fields)
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R^m$ be a **continuous** vector field with $f(0)=0$, and consider the autonomous system
--   $$\dot x=f(x),\qquad x\in\mathbb R^m .$$
--   Suppose there is a $C^1$ function $V:\mathbb R^m\to\mathbb R$ such that
--
--   1. $V$ is positive definite: $V(0)=0$ and $V(x)>0$ for $x\neq0$;
--   2. $V$ is proper (radially unbounded): $V(x)\to+\infty$ as $|x|\to\infty$;
--   3. the derivative of $V$ along $f$ is negative definite: $\frac{\partial V}{\partial x}(x)\,f(x)<0$ for every $x\neq0$.
--
--   Then the origin is a globally asymptotically stable equilibrium of $\dot x=f(x)$: from every initial state there is a solution defined on $[0,\infty)$, no solution escapes to infinity in finite time, the origin is Lyapunov stable and it is uniformly globally attractive, all of these over **every** (possibly non-unique) solution.
--
--   This is Lyapunov's direct method in its global form (Barbashin–Krasovskii), stated for a merely continuous right-hand side, where solutions exist by Peano's theorem but need not be unique. It is the step "Consider the Lyapunov function candidate $U$ … hence the claim" in the proof of Theorem 5.1 of Andrieu–Praly–Astolfi (and in the proofs of Theorems 3.1 and 4.1 there), and it is reusable for any stability proof built on a strict Lyapunov function.
--
--   **Formalization Note** Global asymptotic stability is the notion `IsGAS` of the mission's definition file: the published `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` for the time-invariant field on `EuclideanSpace ℝ (Fin m)`, together with `NoFiniteEscape` (every integral-form solution on a bounded interval $[0,T)$ is bounded there). Positive definiteness, properness (`Tendsto V (cocompact _) atTop`) and negative definiteness are `IsPosDef`, `IsProper`, `IsNegDef` from the same file; the derivative along $f$ is `fderiv ℝ V x (f x)`.
-- source:
--   Used in Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, proof of Theorem 5.1, pp. 23-24 (Lyapunov function (5.12), 'hence the claim'); classical statement: H. K. Khalil, Nonlinear Systems, 3rd ed., Theorem 4.2 (Barbashin-Krasovskii), and A. Bacciotti, L. Rosier, Liapunov Functions and Stability in Control Theory, 2nd ed., Springer 2005, Ch. 2 (continuous right-hand sides, non-unique solutions)

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Lyapunov's direct method (global version, continuous right-hand side): if the continuous
autonomous vector field `f` on `ℝ^m` vanishes at the origin and admits a `C¹`, positive definite
and proper function `V` whose derivative along `f` is negative definite, then the origin is a
globally asymptotically stable equilibrium of `ẋ = f(x)` in the sense of `IsGAS`. -/
theorem lyapunov_sufficient_gas {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (V : (Fin m → ℝ) → ℝ) (hV : ContDiff ℝ 1 V) (hpd : IsPosDef V)
    (hpr : IsProper V) (hneg : IsNegDef (fun x => fderiv ℝ V x (f x))) : IsGAS f := by sorry

end HomogBiLimit.OutputFeedback
