-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_theorem2
-- name    : MifflinSemismooth.Extremal.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:35:23.362241+00:00
-- url     : https://prove2.me/theorems/7dfd256d-8996-4583-8d8a-2423e66f82e9
-- title:
--   Theorem 2, p. 8 — the pointwise max or min of a compact family with continuous bounded ∇ₓf is semismooth on B
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open, $T$ a topological space, $U\subseteq T$ sequentially compact, $f:\mathbb R^n\times T\to\mathbb R$ and $E:\mathbb R^n\to\mathbb R$. Suppose that
--
--   1. (a) $f$ is continuous on $B\times U$;
--   2. either (d) $E(x)=\max\{f(x,u):u\in U\}$ for every $x\in B$, or (d′) $E(x)=\min\{f(x,u):u\in U\}$ for every $x\in B$;
--   3. $f(\cdot,u)$ is differentiable on $B$ for each $u\in U$;
--   4. the partial gradient $\nabla_x f$ is continuous and bounded on $B\times U$.
--
--   Then
--
--   $$E\ \text{is semismooth on}\ B.$$
--
--   That is, at every $x\in B$, $E$ is Lipschitz on a ball about $x$, and for each $d$ and all sequences $t_k\downarrow 0$, $\theta_k/t_k\to 0$, $g_k\in\partial E(x+t_kd+\theta_k)$, the sequence $\{\langle g_k,d\rangle\}$ has exactly one accumulation point. This is the paper's first main result: pointwise maxima and minima over a compact family of continuously differentiable functions, such as min–max objectives, are semismooth, and so fall within the scope of the paper's minimization algorithms.
--
--   **Formalization Note.** Hypotheses (b), (c), (e), (e′) of §3 are not assumed: the paper derives them from the smoothness assumptions. Openness of $B$ is assumed, convexity is not. "Either (d) or (d′)" is read as one of the two forms holding on all of $B$, as in the paper's proof. Joint continuity of $\nabla_x f$ on $B\times U$ is continuity on the product subset, not separate continuity in $x$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 8, §3, Theorem 2

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Theorem 2, p. 8: suppose (a) and (d) or (d') hold, `f(·, u)` is
differentiable on `B` for each `u ∈ U`, and `∇ₓf(·, ·)` is continuous and bounded on `B × U`.
Then `E` is semismooth on `B`. -/
theorem theorem2 {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hdE : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M) :
    SemismoothOn E B := by sorry

end MifflinSemismooth.Extremal
