-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_lemma_2_2_sample_subset
-- name    : NonmonotoneSubmod.RandomSet.lemma_2_2_sample_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:58:33.60298+00:00
-- url     : https://prove2.me/theorems/02c34148-1c20-4dc7-a3c4-258473c47be8
-- title:
--   Lemma 2.2 — $\mathbf{E}[g(A(p))] \ge (1-p)\,g(\emptyset) + p\,g(A)$
-- statement:
--   Let $X$ be a finite ground set and $g : 2^X \to \mathbb{R}$ a submodular function (of any sign). Let $A \subseteq X$ and $p \in [0,1]$, and let $A(p)$ be the random subset of $A$ in which each element of $A$ appears independently with probability $p$. Then
--
--   $$\mathbf{E}[g(A(p))] \ge (1-p)\, g(\emptyset) + p\, g(A).$$
--
--   In words: on a random sample of a fixed set, a submodular function does at least as well as the linear interpolation between its values at the empty set and at the full set. This is the basic probabilistic property of submodular functions on which Lemma 2.3 and the analysis of Algorithm RS rest.
--
--   **Formalization Note** The expectation is the exact finite sum
--   $\mathbf{E}[g(A(p))] = \sum_{T \subseteq A} p^{|T|} (1-p)^{|A \setminus T|}\, g(T)$.
--   The hypothesis $0 \le p \le 1$ is added explicitly; the paper implies it by calling $p$ a probability. It is necessary: for $A = \{a, b\}$ and $g$ equal to $1$ on $\{a\}$ and $\{b\}$ and $0$ on $\emptyset$ and $A$ (submodular), the difference of the two sides is $p(1-p)\cdot 2$, which is negative for $p = 2$.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Lemma 2.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.RandomSet

/-- Lemma 2.2 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `g : 2^X → ℝ` be submodular, `A ⊆ X`,
and let `A(p)` be the random subset of `A` containing each element of `A` independently with
probability `p ∈ [0,1]`. Then `E[g(A(p))] ≥ (1 - p) g(∅) + p g(A)`. The expectation is written as
the exact finite sum over `T ⊆ A` with weight `p^|T| (1-p)^|A \ T|`. -/
theorem lemma_2_2_sample_subset {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by sorry

end NonmonotoneSubmod.RandomSet
