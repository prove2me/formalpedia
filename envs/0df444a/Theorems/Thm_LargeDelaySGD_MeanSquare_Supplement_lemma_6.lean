-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_Supplement_lemma_6
-- name    : LargeDelaySGD.MeanSquare.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:10:44.385944+00:00
-- url     : https://prove2.me/theorems/c8cda119-d76b-4adb-9ab0-ce904bcd4fb5
-- title:
--   Lemma 6, p. 19 — almost surely the affine interpolation A(t) of the DASGD iterates is an asymptotic pseudotrajectory of the flow P
-- statement:
--   Throughout, $\mathcal X\subseteq\mathbb R^d$ is a nonempty compact convex feasible set, $F(x;\omega)$ a random function with $f(x)=\mathbb E[F(x;\omega)]$, $\nabla f(x)=\mathbb E[\nabla F(x;\omega)]$ on $\mathcal X$, $\mathcal X^*$ the set of minimizers of $f$ over $\mathcal X$, and $\mathrm{pr}_{\mathcal X}$ the Euclidean projection onto $\mathcal X$. Assumption 1 is imposed on $\mathcal X$ only, Assumption 3 is mean variational coherence, and Assumption 4 is the printed implication $E(y_n)\to0\Rightarrow\mathrm{pr}_{\mathcal X}(y_n)\to\mathcal X^*$. A sequence converges to $\mathcal X^*$ when its distance to $\mathcal X^*$ tends to $0$.
--
--   Let $\alpha_n$, $s(n)\le n$ satisfy Assumption 2, let $(Y_n)$ be the DASGD iterates of Algorithm 4 driven by i.i.d. samples $\omega_n$ on $(\Omega,\mathbb P)$, let $A(t)$ be their affine interpolation (with $Y_n$ placed at time $\tau_n=\sum_{r=1}^n\alpha_r$), and let $P$ be the semiflow of (17).
--
--   **Lemma 6.** With probability $1$, $A$ is an asymptotic pseudotrajectory of $P$: $A$ is continuous and for every $T>0$
--   $$\lim_{t\to\infty}\ \sup_{0\le h\le T}\big\|A(t+h)-P(h,A(t))\big\|_2=0 .$$
--
--   This relates the random discrete iterates to the deterministic mean dynamics path by path, and is the second ingredient of the proof of Theorem 3.
--
--   **Formalization Note** The asymptotic-pseudotrajectory predicate is the published one (Definition 2, written with $\varepsilon$ and $t_0$ on the time half-line $\mathbb R_{\ge0}$). The almost-sure quantifier is outside the quantifier over $T$.
--
--   Differences from the source:
--   - generalization: Lemma 6 inside §4, under Assumptions 1–4 → Assumptions 3 and 4 are not assumed; reason: the statement does not involve X* or the energy; adding Assumptions 3–4 specializes it to the source
--   - reading: P, the semiflow of the ODE ẏ = −∇f(pr_X(y)) (17), p. 17 → any Flow ℝ≥0 on ℝ^d whose trajectories have right derivative −∇f(pr_X(P(t, y))) at every t ≥ 0; reason: the drift is globally Lipschitz under Assumption 1, so the semiflow exists and is unique; quantifying over every such flow is the source's P
--   - reading: ∇f(x) for x ∈ X, with f defined on X only (Algorithm 5, (6), (17)) → meanGrad F μ x = E[∇F(x; ω)] (a Bochner integral); reason: Remark 1 (p. 5) identifies ∇f with E[∇F]; for f defined only on a compact X the ambient Fréchet gradient may be the junk value 0 at boundary points, the expectation is the source's gradient
--   - reading: Assumption 1 on X: F(·; ω) differentiable for a.a. ω, sup_{x∈X} E‖∇F‖² < ∞, E[∇F] Lipschitz on X → ConstrainedAssumption1: an ambient F(·; ξ) differentiable at every point of X for a.a. ξ, F(x) integrable and ∇F(x) in L² for x ∈ X, ∇F jointly measurable on X × Ξ, a uniform second-moment bound and a Lipschitz mean gradient on X; reason: the source's F lives on X × Ω; its gradient at boundary points presupposes a differentiable extension. Integrability (the expectation in (1) exists) and joint measurability (footnote 1: F is a random function; the iterates must be random variables) only exclude cases where the source's expressions are undefined; nothing is assumed off X
--   - encoding: Assumption 2: d_n = O(n^p) and α_n ∝ φ(n), etc. → the published LargeDelaySGD.MeanSquare.Assumption2 (O(·) as n − s(n) ≤ K (s(n)+1)^q on received gradients, ∝ as eventual proportionality, positive steps, s(n) ≤ n); reason: the encoding of the live mission, reused unchanged; the `+1` and `eventually` only absorb finitely many n where O(·) and ∝ say nothing
--   - reading: delay index s(n) and initial state Y_0 of Algorithm 4 → a deterministic schedule s : ℕ → ℕ with s n ≤ n and a deterministic Y₀ ∈ ℝ^d; reason: the convention of the live mission (s(n) as a given schedule, pp. 8–9); the paper treats s as the algorithm's parameter
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1 (SHA-256 20dd663845757ad1e06f51c4ae62f8fd6623aa921b66be496b00befa51d9a327), p. 19, Lemma 6 and Definition 2 (19) (proof App. B.3, p. 37)

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_LargeDelaySGD_MeanSquare_Supplement_Constrained
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace LargeDelaySGD.MeanSquare.Supplement

theorem lemma_6 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X) (hXne : X.Nonempty)
    (hA1 : ConstrainedAssumption1 F μ X)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hA2 : Assumption2 α s)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω)
    (Y₀ : EuclideanSpace ℝ (Fin d)) (Y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hY : IsLazyDASGD F X α s ω Y₀ Y)
    (Pf : Flow ℝ≥0 (EuclideanSpace ℝ (Fin d))) (hP : IsMeanFieldFlow F μ X Pf) :
    ∀ᵐ a ∂P, StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Pf
      (affineInterp α (fun n => Y n a)) := by sorry

end LargeDelaySGD.MeanSquare.Supplement
