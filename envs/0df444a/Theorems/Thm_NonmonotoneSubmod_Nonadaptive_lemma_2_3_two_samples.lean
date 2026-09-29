-- Prove2me | Theorems.Thm_NonmonotoneSubmod_Nonadaptive_lemma_2_3_two_samples
-- name    : NonmonotoneSubmod.Nonadaptive.lemma_2_3_two_samples
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T06:23:45.696066+00:00
-- url     : https://prove2.me/theorems/fbff2f7b-b2c4-4a2e-9c5d-e8394c65d0b2
-- title:
--   Lemma 2.3 — union of two independently sampled subsets
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be submodular, let $A, B \subseteq X$ be two (not necessarily disjoint) sets, and let $A(p)$ and $B(q)$ be independently sampled subsets, where each element of $A$ appears in $A(p)$ independently with probability $p$ and each element of $B$ appears in $B(q)$ independently with probability $q$, with $p, q \in [0,1]$. Then
--
--   $$
--   \mathbf{E}[f(A(p) \cup B(q))] \ge (1-p)(1-q)\, f(\emptyset) + p(1-q)\, f(A) + (1-p)q\, f(B) + pq\, f(A \cup B).
--   $$
--
--   It is the two-set version of Lemma 2.2 and is the tool used to bound the expected value of $f$ on a uniformly random set from below by values of $f$ at a few deterministic sets.
--
--   **Formalization Note** The expectation over the pair of independent samples is the exact double sum
--   $\sum_{S \subseteq A}\sum_{T \subseteq B} p^{|S|}(1-p)^{|A\setminus S|}\, q^{|T|}(1-q)^{|B\setminus T|}\, f(S \cup T)$, which is correct also when $A$ and $B$ overlap. The ranges $0 \le p, q \le 1$ are stated explicitly. No sign condition on $f$ is assumed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Lemma 2.3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.Nonadaptive

/-- Lemma 2.3 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `f : 2^X → ℝ` be submodular, let
`A, B ⊆ X` be two (not necessarily disjoint) sets, and let `A(p)`, `B(q)` be independently sampled
subsets (each element of `A` in `A(p)` with probability `p`, each element of `B` in `B(q)` with
probability `q`). Then
`E[f(A(p) ∪ B(q))] ≥ (1-p)(1-q) f(∅) + p(1-q) f(A) + (1-p)q f(B) + pq f(A ∪ B)`.
The expectation over the pair of independent samples is the exact double sum over `S ⊆ A`,
`T ⊆ B` with weights `p^|S| (1-p)^|A \ S|` and `q^|T| (1-q)^|B \ T|`. -/
theorem lemma_2_3_two_samples {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (A B : Finset X) (p q : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - p) * (1 - q) * f ∅ + p * (1 - q) * f A + (1 - p) * q * f B + p * q * f (A ∪ B) ≤
      ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
        (p ^ S.card * (1 - p) ^ (A \ S).card) * (q ^ T.card * (1 - q) ^ (B \ T).card) *
          f (S ∪ T) := by sorry

end NonmonotoneSubmod.Nonadaptive
