-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_lemma_2_2_sample_subset
-- name    : NonmonotoneSubmod.Nonadaptive.lemma_2_2_sample_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:19:19.624514+00:00
-- url     : https://prove2.me/theorems/571959d8-3ace-4718-b696-32db111f70ce
-- title:
--   Lemma 2.2 — random subsets of a set, one sample
-- statement:
--   Let $g : 2^X \to \mathbb{R}$ be submodular, let $A \subseteq X$, and let $A(p)$ be the random subset of $A$ in which each element of $A$ appears independently with probability $p \in [0,1]$. Then
--
--   $$
--   \mathbf{E}[g(A(p))] \ge (1 - p)\, g(\emptyset) + p\, g(A).
--   $$
--
--   The expected value of a submodular function on a random subset of $A$ is at least the corresponding average of its values at the two extreme subsets $\emptyset$ and $A$. It is the basic probabilistic property of submodular functions on which all the sampling estimates of the paper rest.
--
--   **Formalization Note** The expectation is the exact finite sum $\sum_{T \subseteq A} p^{|T|}(1-p)^{|A \setminus T|}\, g(T)$. The hypothesis $0 \le p \le 1$ is implicit in "with probability $p$" and is stated explicitly; the lemma fails for $p$ outside $[0,1]$. No sign condition on $g$ is assumed, as on the page.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Lemma 2.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.Nonadaptive

/-- Lemma 2.2 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `g : 2^X → ℝ` be submodular, `A ⊆ X`,
and let `A(p)` be the random subset of `A` containing each element of `A` independently with
probability `p ∈ [0,1]`. Then `E[g(A(p))] ≥ (1 - p) g(∅) + p g(A)`. The expectation is written as
the exact finite sum over `T ⊆ A` with weight `p^|T| (1-p)^|A \ T|`. -/
theorem lemma_2_2_sample_subset {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by sorry

end NonmonotoneSubmod.Nonadaptive
