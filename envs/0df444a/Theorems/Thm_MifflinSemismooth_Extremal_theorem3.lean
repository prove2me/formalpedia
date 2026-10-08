-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_theorem3
-- name    : MifflinSemismooth.Extremal.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:35:07.503668+00:00
-- url     : https://prove2.me/theorems/d61cefdd-8ff1-4c42-83d1-6304d1ea79a5
-- title:
--   Theorem 3, p. 10 — a max over a compact family of functions semiconvex at x is semiconvex at x
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open, $T$ a topological space, $U\subseteq T$ sequentially compact, $f:\mathbb R^n\times T\to\mathbb R$ and $E:\mathbb R^n\to\mathbb R$, and assume hypotheses (a), (b), (c), (d), (e) of §3, so that $E$ is a max function: $E(x)=\max\{f(x,u):u\in U\}$ on $B$. Let $X\subseteq B$ and $x\in X$, and suppose that $f(\cdot,u)$ is semiconvex at $x$ with respect to $X$ for each $u\in U$. Then
--
--   $$E\ \text{is semiconvex at}\ x\ \text{with respect to}\ X.$$
--
--   Thus semiconvex functions, like convex ones and unlike pseudoconvex ones, are preserved under pointwise maximization over a compact family. The result feeds the optimality theory of §5, where problem functions are required to be semiconvex.
--
--   **Formalization Note.** Semiconvexity is Definition 2 of the mission's `Basic` file; the condition "$E'(x;d)\ge 0$" in it means that $E'(x;d)$ exists and is nonnegative.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 10, §3, Theorem 3

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Theorem 3, p. 10: let `X ⊆ B`; under (a), (b), (c), (d), (e), if `f(·, u)` is
semiconvex at `x ∈ X` (with respect to `X`) for each `u ∈ U`, then `E` is semiconvex at `x`
(with respect to `X`). -/
theorem theorem3 {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hb : HypB B U f) (hc : HypC B U f) (hd : HypD B U f E)
    (he : HypE B U f) (X : Set (EuclideanSpace ℝ (Fin n))) (hXB : X ⊆ B)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hsc : ∀ u ∈ U, SemiconvexAt X (fun y => f y u) x) :
    SemiconvexAt X E x := by sorry

end MifflinSemismooth.Extremal
