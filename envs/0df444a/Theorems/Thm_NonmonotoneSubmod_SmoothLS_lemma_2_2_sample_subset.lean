-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_lemma_2_2_sample_subset
-- name    : NonmonotoneSubmod.SmoothLS.lemma_2_2_sample_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:08:36.752906+00:00
-- url     : https://prove2.me/theorems/172b7dbf-0f8c-4836-b573-bd202e3f96f2
-- title:
--   Lemma 2.2 — $\mathbf{E}[g(A(p))] \ge (1-p)g(\emptyset) + p\,g(A)$
-- statement:
--   Let $g : 2^X \to \mathbb{R}$ be submodular on a finite ground set $X$, let $A \subseteq X$, and let $A(p)$ be the random subset of $A$ in which each element of $A$ appears independently with probability $p \in [0,1]$. Then
--
--   $$
--   \mathbf{E}[g(A(p))] \ge (1-p)\, g(\emptyset) + p\, g(A).
--   $$
--
--   This is the basic probabilistic property of submodular functions on which all later sampling estimates of the paper, in particular display (∗), are built by iteration.
--
--   **Formalization Note** The expectation is the exact finite sum $\sum_{T \subseteq A} p^{|T|}(1-p)^{|A\setminus T|} g(T)$. The hypothesis $0 \le p \le 1$ is implicit in "with probability $p$" and is stated explicitly; $g$ carries no sign assumption, as printed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1137, Lemma 2.2

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.SmoothLS

/-- Lemma 2.2 (Feige–Mirrokni–Vondrák 2011, p. 1137). Let `g : 2^X → ℝ` be submodular, `A ⊆ X`,
and let `A(p)` be the random subset of `A` containing each element of `A` independently with
probability `p ∈ [0,1]`. Then `E[g(A(p))] ≥ (1 - p) g(∅) + p g(A)`. The expectation is written as
the exact finite sum over `T ⊆ A` with weight `p^|T| (1-p)^|A \ T|`. -/
theorem lemma_2_2_sample_subset {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by sorry

end NonmonotoneSubmod.SmoothLS
