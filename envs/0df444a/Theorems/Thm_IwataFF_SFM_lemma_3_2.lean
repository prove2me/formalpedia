-- Prove2me | Theorems.Thm_IwataFF_SFM_lemma_3_2
-- name    : IwataFF.SFM.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:39.906993+00:00
-- url     : https://prove2.me/theorems/f39dadef-5555-4a26-8f2f-817666075269
-- title:
--   Lemma 3.2 — relaxed weak duality: $z^-(V) \le f(X) + \binom{n}{2}\delta$
-- statement:
--   Let $V$ be a finite nonempty set with $|V| = n$ and $f$ submodular on $V$ with $f(\emptyset) = 0$. Let $x \in B(f)$ be a base, $\delta > 0$, and $\varphi : V \times V \to \mathbb{R}$ a skew-symmetric, $\delta$-feasible flow ($\varphi(u,v) + \varphi(v,u) = 0$ and $-\delta \le \varphi(u,v) \le \delta$ for $u, v \in V$). Then $z = x - \partial\varphi$, with $\partial\varphi(v) = \sum_{u \in V}\varphi(u,v)$, satisfies
--   $$z^-(V) \le f(X) + \binom{n}{2}\delta \qquad \text{for every } X \subseteq V.$$
--
--   **Formalization Note** $f$ is real-valued (§3 assumes integer values; the proof never uses them). $\binom{n}{2}$ is `Nat.choose (card V) 2` cast to the reals.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, p. 10, Lemma 3.2

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic

namespace IwataFF.SFM

/-- Lemma 3.2 (arXiv:math/0004089v1, p. 10): for any base `x ∈ B(f)` and any δ-feasible
(skew-symmetric) flow `ϕ`, `z = x − ∂ϕ` satisfies `z⁻(V) ≤ f(X) + C(n,2) δ` for every `X ⊆ V`. -/
theorem lemma_3_2 {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (x : α → ℝ) (hx : x ∈ basePoly V f) (phi : α → α → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hskew : ∀ u ∈ V, ∀ v ∈ V, phi u v + phi v u = 0)
    (hfeas : ∀ u ∈ V, ∀ v ∈ V, -δ ≤ phi u v ∧ phi u v ≤ δ)
    (X : Finset α) (hX : X ⊆ V) :
    xsum (xneg (fun v => x v - ∑ u ∈ V, phi u v)) V ≤
      f X + ((V.card.choose 2 : ℕ) : ℝ) * δ := by sorry

end IwataFF.SFM
