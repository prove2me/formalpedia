-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConcreteFactors_both_nonzero
-- name    : OAI.TorsionFreeZeroDivisors.ConcreteFactors.both_nonzero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:13:24.596046+00:00
-- url     : https://prove2.me/theorems/2a4a5f25-3951-40c0-9a42-776cc5084021
-- title:
--   Section 6 (OpenAI) — on a good sample, both zero-divisor factors $\alpha$ and $\beta$ are nonzero
-- statement:
--   Let $r=(r_A,r_B)$ be a pair of matchings at level $n$, and let $x$, $y$ be vertices of sides $A$ and $B$. Assume
--
--   1. $L=L(\mathrm{size}(n))\ge2$;
--   2. every connected component of both vertex graphs has diameter at most $D_0L$;
--   3. $r\in\mathcal S(n)$: both graphs have girth at least $L$;
--   4. the sampled graph carries no bounded system rooted at $x,y$ with OpenAI's fixed parameters $(C,K,I)$ of Section 4.
--
--   Let $G$ be the group of the sampled graph coned off: generators the $8258$ letter pairs, and one relator per dart saying that the label of the dart agrees with the chosen route labels at its ends. For a vertex $a$ in the component $C_A$ of $x$, let $g_a=[x]^{-1}[a]\in G$ be the label of a path from $x$ to $a$. Define $h_b$ for $b$ in the component $C_B$ of $y$ in the same way. Put
--
--   $$\alpha=\sum_{a\in C_A}g_a,\qquad \beta=\sum_{b\in C_B}h_b^{-1}\qquad\text{in }\mathbb F_2[G].$$
--
--   Then $\alpha\neq0$ and $\beta\neq0$.
--
--   These are the factors of Theorem 1.1. The proof shows that the root is the only vertex whose label is the identity, so the identity coefficient of each factor is $1$. Together with the cancellation $\alpha\beta=0$ and torsion-freeness, this gives `OAIKaplansky.exists_torsionFree_zero_divisors`.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 24: “Set $\alpha = \sum_{x\in A'} g_x$, $\beta = \sum_{y\in B'} h_y^{-1}$ in $\mathbb F_2[G]$. Both sums are finite. The root contributes the identity to each. By Proposition 5.1, no other vertex contributes identity, so its coefficient is one in each factor. Thus $\alpha \neq 0$ and $\beta \neq 0$.” Proposition 5.1 (p. 20): “Moreover, if a path in $\Gamma$ starts at $x_A$ or $x_B$ and ends at a different vertex, its label is nontrivial in $G$.”
--
--   **Formalization note.** The objects are OpenAI's (`ConcreteFactors.alpha` and `beta`, `ConcreteGroup.G`, `SampleGraph.BoundedSystem`, `GraphSample.Diameters`, `ActualPatternEvent.samples`, with the constants of Section 4, from the bundle `Def_TorsionFreeZeroDivisorsConstruction`). The group is a Mathlib `PresentedGroup`. It depends on routes (a base vertex per component and a path to each vertex) and on the letter pairing, all fixed by choice and not otherwise specified. Girth is stated in the subdivision graph as $\ge3L$. Coefficients are in $\mathbb Z/2$, so $\alpha\ne0$ says that some group element occurs an odd number of times.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 24, proof of Theorem 1.1 (α ≠ 0 and β ≠ 0, from Proposition 5.1); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), ConcreteFactors.both_nonzero

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.ConcreteFactors

open scoped Classical
open SampleGraph

theorem both_nonzero {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
    (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
    (hsample : r∈ActualPatternEvent.samples rep)
    (havoid : IsEmpty (BoundedSystem (PlanarParameters.C PathSystem.ε ClosedWords.D)
      (PlanarParameters.K PathSystem.ε ClosedWords.D) (PlanarParameters.sides PathSystem.ε ClosedWords.D) rep r x y)) :
    alpha rep r x≠0 ∧ beta rep r y≠0 := by
  sorry

end OAI.TorsionFreeZeroDivisors.ConcreteFactors
