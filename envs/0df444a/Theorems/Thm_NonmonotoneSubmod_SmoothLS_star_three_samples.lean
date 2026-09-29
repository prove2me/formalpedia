-- Prove2me | Theorems.Thm_NonmonotoneSubmod_SmoothLS_star_three_samples
-- name    : NonmonotoneSubmod.SmoothLS.star_three_samples
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:09:02.07726+00:00
-- url     : https://prove2.me/theorems/4ee9dc16-b838-4bbd-a5a4-43f20351adbb
-- title:
--   §3.2, display (∗) — three independently sampled sets
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be submodular on a finite ground set $X$, let $A_1, A_2, A_3 \subseteq X$ be arbitrary (not necessarily disjoint), and let $A_1(p_1), A_2(p_2), A_3(p_3)$ be independently sampled subsets, each element of $A_i$ appearing in $A_i(p_i)$ with probability $p_i \in [0,1]$. Then
--
--   $$
--   \mathbf{E}\big[f(A_1(p_1) \cup A_2(p_2) \cup A_3(p_3))\big] \ge \sum_{I \subseteq \{1,2,3\}} \prod_{i \in I} p_i \prod_{i \notin I} (1-p_i)\, f\Big(\bigcup_{i \in I} A_i\Big).
--   $$
--
--   This extension of Lemma 2.3 to three sets is the tool that lower-bounds $\mathbf{E}[f(R \cap (B \cup C))]$ and $\mathbf{E}[f(R \cup (B \cap C))]$ in the analysis of Algorithm SLS.
--
--   **Formalization Note** The indices $1,2,3$ are `0, 1, 2 : Fin 3`. The expectation over the three independent samples is the exact triple sum over $S_i \subseteq A_i$ with weights $p_i^{|S_i|}(1-p_i)^{|A_i \setminus S_i|}$; the right side sums over all $I$ with $\bigcup_{i\in\emptyset} A_i = \emptyset$. The hypotheses $0 \le p_i \le 1$ are stated explicitly.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1143, §3.2, display (∗)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.SmoothLS

/-- §3.2, display (∗) (Feige–Mirrokni–Vondrák 2011, p. 1143), the three-set extension of
Lemma 2.3. Let `f : 2^X → ℝ` be submodular, let `A₁, A₂, A₃ ⊆ X` (here `A 0, A 1, A 2`, not
necessarily disjoint) and let `A_i(p_i)` be independently sampled subsets, each element of `A_i`
appearing in `A_i(p_i)` with probability `p_i ∈ [0,1]`. Then
`E[f(A₁(p₁) ∪ A₂(p₂) ∪ A₃(p₃))] ≥ ∑_{I ⊆ {1,2,3}} ∏_{i ∈ I} p_i ∏_{i ∉ I} (1 - p_i) f(⋃_{i ∈ I} A_i)`.
The expectation over the three independent samples is the exact triple sum over `S_i ⊆ A_i`
with weights `p_i^|S_i| (1 - p_i)^|A_i \ S_i|`. -/
theorem star_three_samples {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Fin 3 → Finset X) (p : Fin 3 → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∑ I : Finset (Fin 3), (∏ i ∈ I, p i) * (∏ i ∈ Iᶜ, (1 - p i)) * f (I.biUnion A) ≤
      ∑ S₁ ∈ (A 0).powerset, ∑ S₂ ∈ (A 1).powerset, ∑ S₃ ∈ (A 2).powerset,
        (p 0 ^ S₁.card * (1 - p 0) ^ (A 0 \ S₁).card) *
          (p 1 ^ S₂.card * (1 - p 1) ^ (A 1 \ S₂).card) *
          (p 2 ^ S₃.card * (1 - p 2) ^ (A 2 \ S₃).card) * f (S₁ ∪ S₂ ∪ S₃) := by sorry

end NonmonotoneSubmod.SmoothLS
