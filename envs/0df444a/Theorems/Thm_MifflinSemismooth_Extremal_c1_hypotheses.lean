-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_c1_hypotheses
-- name    : MifflinSemismooth.Extremal.c1_hypotheses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:36:16.071275+00:00
-- url     : https://prove2.me/theorems/e026cbef-d6f0-4205-9e6b-0d9deb4c1a76
-- title:
--   Proof of Theorem 2, p. 8 — a continuous bounded ∇ₓf gives (c), (e), (e′), ∂ₓf = {∇ₓf}, and (b) on balls in B
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open, $T$ a topological space, $U\subseteq T$ and $f:\mathbb R^n\times T\to\mathbb R$. Suppose $f(\cdot,u)$ is differentiable at every point of $B$ for each $u\in U$, and that the partial gradient $\nabla_x f$ is continuous on $B\times U$ (jointly) and bounded there: $|\nabla_x f(x,u)|\le M$. Then:
--
--   1. hypothesis (c) holds: $\partial_x f$ is upper semicontinuous on $B\times U$;
--   2. hypotheses (e) and (e′) hold: for all $x\in B$, $u\in U$, $d$, the derivative $f'_x(x,u;d)$ exists and equals both $f^0_x(x,u;d)$ and $-f^0_x(x,u;-d)$;
--   3. $\partial_x f(x,u)=\{\nabla_x f(x,u)\}$ for all $(x,u)\in B\times U$;
--   4. hypothesis (b) holds on every ball inside $B$: if the open ball $B(x,r)$ is contained in $B$, there is $K$ with $f(\cdot,u)$ $K$-Lipschitz on $B(x,r)$ for every $u\in U$.
--
--   These are the facts the proof of Theorem 2 opens with ("the additional assumption implies (b), (c), (e), and (e′) and $\partial_x f=\nabla_x f$ on $B\times U$"); they let Theorem 1 be applied to the continuously differentiable case.
--
--   **Formalization Note.** The page claims (b) on all of $B$. A bounded gradient gives a uniform Lipschitz constant only on convex subsets of $B$ (the polar angle on a slit annulus is a counterexample on a non-convex open set), so (b) is stated on balls contained in $B$; this is all the proof of Theorem 2 needs, because its conclusion is local and Theorem 1 can be applied on a ball about $x$. "$\partial_x f=\nabla_x f$" is read as $\partial_x f(x,u)=\{\nabla_x f(x,u)\}$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 8, §3, proof of Theorem 2, first sentence

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), proof of Theorem 2, p. 8: if `f(·, u)` is differentiable on the open set `B`
for each `u ∈ U` and `∇ₓf` is continuous and bounded on `B × U`, then (c), (e) and (e') hold,
`∂ₓf = {∇ₓf}` on `B × U`, and (b) holds on every ball contained in `B`. -/
theorem c1_hypotheses {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (hB : IsOpen B)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M) :
    HypC B U f ∧ (HypE B U f ∧ HypE' B U f) ∧
    (∀ x ∈ B, ∀ u ∈ U, partialGenGrad f x u = {gradient (fun y => f y u) x}) ∧
    (∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), Metric.ball x r ⊆ B →
      ∃ K : NNReal, ∀ u ∈ U, LipschitzOnWith K (fun y => f y u) (Metric.ball x r)) := by sorry

end MifflinSemismooth.Extremal
