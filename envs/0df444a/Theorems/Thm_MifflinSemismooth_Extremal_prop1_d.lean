-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop1_d
-- name    : MifflinSemismooth.Extremal.prop1_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:25.414925+00:00
-- url     : https://prove2.me/theorems/1c374c08-868a-4c93-b7ff-5543f948e6a2
-- title:
--   Proposition 1(d), p. 3 — ∂F is bounded by K and uppersemicontinuous on B
-- statement:
--   Let $B\subseteq\mathbb R^n$ be open, let $F:\mathbb R^n\to\mathbb R$ be Lipschitz on $B$ with constant $K$, and let $x\in B$. Suppose $\{x_k\}\subseteq B$ converges to $x$ and $g_k\in\partial F(x_k)$ for each $k$. Then
--
--   $$|g_k|\le K\ \text{for every } k,\qquad\text{and every accumulation point } g \text{ of } \{g_k\} \text{ satisfies } g\in\partial F(x).$$
--
--   In words: $\partial F$ is bounded on bounded subsets of $B$ and upper semicontinuous on $B$. This is the property that, in the proof of Theorem 2, turns accumulation points of generalized gradients of $E$ near $x$ into elements of $\partial E(x)$.
--
--   **Formalization Note.** $K$ is the Lipschitz constant of $F$ on $B$, as on the page. "Accumulation point" is a cluster point of the sequence (`MapClusterPt`).
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 3, Proposition 1(d)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 1(d), p. 3: if `{x_k} ⊂ B` converges to `x` and
`g_k ∈ ∂F(x_k)`, then `|g_k| ≤ K` and every accumulation point of `{g_k}` lies in `∂F(x)`. -/
theorem prop1_d {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hB : IsOpen B) (K : NNReal) (hFB : LipschitzOnWith K F B) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ B) :
    ∀ (xs gs : ℕ → EuclideanSpace ℝ (Fin n)), (∀ k, xs k ∈ B) → Tendsto xs atTop (𝓝 x) →
      (∀ k, gs k ∈ genGrad F (xs k)) →
      (∀ k, ‖gs k‖ ≤ K) ∧ ∀ g, MapClusterPt g atTop gs → g ∈ genGrad F x := by sorry

end MifflinSemismooth.Extremal
