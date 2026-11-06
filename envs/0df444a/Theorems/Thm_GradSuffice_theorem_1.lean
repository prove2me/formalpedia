-- Prove2me | Theorems.Thm_GradSuffice_theorem_1
-- name    : GradSuffice.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:04.982696+00:00
-- url     : https://prove2.me/theorems/5fd76f62-2086-4eeb-a990-24c1c85b713c
-- title:
--   Theorem 1, pp.7–8 — optimizability of a Banach unit ball ⇔ bounded shattered trees ⇔ Rademacher decay ⇔ M-type ⇔ uniformly convex regularizer
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$ and $B^\star$ its dual unit ball.
--
--   **Theorem 1.** The following are equivalent:
--   1. $B$ is optimizable: for every $\varepsilon>0$ some (possibly randomized) first-order algorithm with finitely many queries is $\varepsilon$-accurate for every convex 1-Lipschitz objective and every valid oracle.
--
--      1′. $B$ is deterministically optimizable (the same with deterministic algorithms, which must succeed on every run).
--   2. $B$ has uniformly bounded shattered trees: for every $\theta>0$ the depths of the $B^\star$-valued trees shattered by $B$ at margin $\theta$ are bounded.
--   3. The sequential Rademacher complexity decays polynomially: for some $q\ge2$ and $C$,
--   $$\mathcal R^{(s)}_m(B)\le C\,m^{-1/q}\qquad(m\ge1).$$
--   4. $B^\star$ has M-type $p$ for some $1<p\le2$.
--   5. There is a continuous convex function $R$ on $B$ with $0\le R\le1$ that is uniformly convex of power type: for some $c>0$ and $q\ge2$,
--   $$R\Big(\frac{w_1+w_2}2\Big)+c\|w_1-w_2\|^q\le\frac{R(w_1)+R(w_2)}2\qquad(w_1,w_2\in B).$$
--
--   The theorem characterizes the Banach spaces whose unit ball can be optimized with finitely many gradient queries at every accuracy; the new implication is 1 → 2 (Theorem 4), together with a quantitative 2 → 3 (Theorem 3).
--
--   **Formalization Note** Optimization is in the oracle model of §2: objectives are convex 1-Lipschitz functions on an open convex neighbourhood of $B$, the oracle is any subgradient selection, the output is the last of $T\ge1$ queries, and a randomized algorithm is a family of deterministic ones indexed by a probability space, with measurable success sets.
--
--   Differences from the source:
--   - generalization: five equivalent items → six: item 1 split into randomized optimizability (1) and deterministic optimizability (1′); reason: (1′) implies (1); the paper's route 5 → 1 is Mirror Descent, a deterministic method, so any reading of "algorithm" between deterministic and randomized gives the paper's equivalence
--   - encoding: R⁽ˢ⁾ₘ(B) decays as O(m^{−1/q}) → seqRad ξ ≤ C m^{−1/q} for every m ≥ 1 and every B⋆-valued ξ of length m; reason: R⁽ˢ⁾ₘ(B) ≤ 1, so a bound for large m extends to all m ≥ 1 with a larger C (p.6's "polynomially bounded")
--   - reading: R : B → ℝ "1-bounded" → 0 ≤ R ≤ 1 on B; reason: as in the §2 Theorem (ii), "0 ≤ R(w) ≤ 1 on B"; the alternative |R| ≤ 1 is equivalent through R ↦ (R + 1)/2
--   - reading: "uniformly-convex … with bounded power type" → ∃ c > 0, q ≥ 2 with NondualOpt.IsUnifConvexOn B R c q; reason: p.5: power type q ≥ 2 is (C, q)-uniform convexity, i.e. c = (1/(2C))^q
--   - reading: "a first-order oracle O receives a point w ∈ W and returns a pair (f(w), ξ), where ξ ∈ ∂f(w) … the oracle may return any of them" → an oracle is a fixed subgradient selection w ↦ g(w), and algorithms must succeed for every such selection; reason: p.4 defines the oracle as a map from the queried point to the answer
--   - encoding: "optimizable" in the model of §2, p.4 → objectives (U, f) with U an open convex neighbourhood of B; last of T ≥ 1 queries as output; randomized algorithms over a probability space with measurable success sets; reason: the model of p.4 read literally; a probability is only defined for measurable sets
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 1, pp.7–8

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_IsUnifConvexOn
import Definitions.Def_GradSuffice_Optimizable
import Definitions.Def_GradSuffice_DetOptimizable
import Definitions.Def_GradSuffice_UniformlyBoundedShatteredTrees
import Definitions.Def_GradSuffice_seqRad
import Definitions.Def_GradSuffice_HasMType

namespace GradSuffice

/-- **Theorem 1 (qualitative characterization).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 1, pp.7–8: "Let `B` be the unit ball
of a real Banach space `X`, and let `B⋆` be its dual unit ball. Then the following are equivalent:
1. `B` is optimizable. 2. `B` has uniformly bounded shattered trees. 3. The normalized sequential
Rademacher complexity of `B` decays as `O(m^{−1/q})` for some `q ≥ 2`. 4. `B⋆` has bounded `p` M-type
for some `1 < p ≤ 2`. 5. There exists a continuous, convex, 1-bounded, uniformly-convex function
`R : B → ℝ` with bounded power type."

**Formalization Note.** Six equivalent entries: (1) randomized optimizability, (1′) deterministic
optimizability (a stronger variant, added), (2)–(5) as printed. (3): `R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q}` for all
`m ≥ 1` (equivalent to `O(m^{−1/q})` since `R⁽ˢ⁾ₘ(B) ≤ 1`), stated for every `B⋆`-valued
adaptive sequence. (5): "1-bounded" is `0 ≤ R ≤ 1` on `B` and "bounded power type" is
`(C, q)`-uniform convexity with `q ≥ 2` (p.5), i.e. `NondualOpt.IsUnifConvexOn B R c q` with
`c = (1/(2C))^q > 0`. -/
theorem theorem_1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    List.TFAE
      [ Optimizable X (Metric.closedBall (0 : X) 1),
        DetOptimizable X (Metric.closedBall (0 : X) 1),
        UniformlyBoundedShatteredTrees X,
        ∃ q : ℝ, 2 ≤ q ∧ ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m,
          IsDualValued ξ → seqRad ξ ≤ C * (m : ℝ) ^ (-1 / q),
        ∃ p : ℝ, 1 < p ∧ p ≤ 2 ∧ ∃ C : ℝ, HasMType X p C,
        ∃ R : X → ℝ, ContinuousOn R (Metric.closedBall (0 : X) 1) ∧ ConvexOn ℝ (Metric.closedBall (0 : X) 1) R ∧
          (∀ w ∈ Metric.closedBall (0 : X) 1, 0 ≤ R w ∧ R w ≤ 1) ∧
          ∃ c : ℝ, 0 < c ∧ ∃ q : ℝ, 2 ≤ q ∧ NondualOpt.IsUnifConvexOn (Metric.closedBall (0 : X) 1) R c q ] := by sorry

end GradSuffice
