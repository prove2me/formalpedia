-- Prove2me | Theorems.Thm_Intersectionality_Reductive_poincare_miranda_step
-- name    : Intersectionality.Reductive.poincare_miranda_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:59.242066+00:00
-- url     : https://prove2.me/theorems/83cc4218-52c1-47a5-97d6-2dd02cdad5ad
-- title:
--   Appendix D — (5) gives θ* ∈ [a, b] with Rᵢ(θ*, t(θ*)) = α for all i, hence a nonintersectional reductive representative policy
-- statement:
--   Work in the model of the Setting: $X \subset \mathbb{R}$ an interval, $n \ge 2$, $\alpha \in (0,1)$, and $Q$ a rich and commutative family of strictly increasing bijections of $X$. Let $p \in P$ and $x_0 \in X$. Let $a, b \in X^n$ satisfy $a_j \le b_j$ for all $j$ and condition (5). Then there is $\theta^* \in X^n$ such that:
--
--   1. $a_i \le \theta^*_i \le b_i$ for all $i$;
--   2. $R_i(\theta^*, t(\theta^*)) = \alpha$ for all $i$;
--   3. every map $r_g(\cdot \mid \theta^*)$ lies in $Q$, and the policy $g \mapsto r_g(\cdot \mid \theta^*)$ is nonintersectional;
--   4. this policy, with threshold $x^* = t(\theta^*)$, satisfies the capacity constraint and achieves a reductive representative outcome:
--   $$\hat p(g_i) = p(g_i) \quad \text{for all } i.$$
--
--   This is the step of the proof of Proposition 3 that turns condition (5) into a policy; the paper obtains $\theta^*$ from the Poincaré–Miranda theorem.
--
--   **Formalization Note.** The hypothesis $a \le b$ is implicit on the page ("$\theta^* \in [a, b]$") and is added explicitly. Without it some box $\times_{j \ne i}[a_j, b_j]$ could be empty, (5) would hold vacuously for that $i$, and the conclusion would fail.
-- source:
--   Carvalho, Pradelski and Williams, Intersectionality: Affirmative Action with Multidimensional Identities, hal-04788142v1, p. 25 (PDF 26), Appendix D, "When (5) holds, the Poincaré-Miranda Theorem provides"

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

namespace Intersectionality.Reductive

/-- Appendix D, p. 25: if `p ∈ P` satisfies (5) for `a ≤ b`, there is `θ* ∈ [a, b]` with
`Rᵢ(θ*, t(θ*)) = α` for all `i`, and the nonintersectional policy `r_g(· | θ*)` with the threshold
`t(θ*)` achieves a reductive representative outcome. -/
theorem poincare_miranda_step (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ)
    (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) (p : Intersectionality.Generic.DistSpace X n) (x0 : ↥X) (a b : Fin n → ↥X)
    (hab : ∀ j, a j ≤ b j) (h5 : Cond5 p.1 Q x0 α a b) :
    ∃ θs : Fin n → ↥X, (∀ i, a i ≤ θs i ∧ θs i ≤ b i) ∧
      (∀ i, catRate p.1 Q x0 θs (thr p.1 Q x0 α θs) i = α) ∧
      (∀ g, grpMap Q x0 θs g ∈ Q) ∧ Intersectionality.Generic.IsNonintersectional (grpMap Q x0 θs) ∧
      IsReductiveRepresentative p.1 α (grpMap Q x0 θs) (thr p.1 Q x0 α θs) := by sorry

end Intersectionality.Reductive
