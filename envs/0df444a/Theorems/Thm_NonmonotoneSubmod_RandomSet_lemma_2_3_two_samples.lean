-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_lemma_2_3_two_samples
-- name    : NonmonotoneSubmod.RandomSet.lemma_2_3_two_samples
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:59:13.328977+00:00
-- url     : https://prove2.me/theorems/ed54c9d3-cbb3-4f06-a30c-f382ff3047bb
-- title:
--   Lemma 2.3 — $\mathbf{E}[f(A(p) \cup B(q))]$ bounded below by the four corners
-- statement:
--   Let $X$ be a finite ground set and $f : 2^X \to \mathbb{R}$ a submodular function (of any sign). Let $A, B \subseteq X$ be two sets, not necessarily disjoint, and $p, q \in [0,1]$. Let $A(p)$ and $B(q)$ be independently sampled subsets: each element of $A$ appears in $A(p)$ independently with probability $p$, each element of $B$ appears in $B(q)$ independently with probability $q$, and the two samples are independent of each other. Then
--
--   $$\mathbf{E}[f(A(p) \cup B(q))] \ge (1-p)(1-q)\, f(\emptyset) + p(1-q)\, f(A) + (1-p)q\, f(B) + pq\, f(A \cup B).$$
--
--   The right-hand side is the bilinear interpolation of $f$ between the four "corners" $\emptyset$, $A$, $B$, $A \cup B$. The lemma is the tool behind the analyses of the random set algorithm (Theorem 2.1), the nonadaptive algorithm (Theorem 2.6) and smooth local search (Theorem 3.6).
--
--   **Formalization Note** The expectation over the pair of independent samples is the exact double sum
--   $$\sum_{S \subseteq A} \sum_{T \subseteq B} p^{|S|}(1-p)^{|A \setminus S|}\; q^{|T|}(1-q)^{|B \setminus T|}\; f(S \cup T).$$
--   Overlapping $A$ and $B$ are allowed, as printed; an element of $A \cap B$ then lies in $A(p) \cup B(q)$ with probability $1-(1-p)(1-q)$, which the double sum accounts for. The hypotheses $0 \le p, q \le 1$ are added explicitly; the paper implies them by calling $p, q$ probabilities.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Lemma 2.3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.RandomSet

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

end NonmonotoneSubmod.RandomSet
