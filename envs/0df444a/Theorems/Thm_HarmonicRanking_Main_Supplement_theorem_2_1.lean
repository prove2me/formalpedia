-- Prove2me | Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_2_1
-- name    : HarmonicRanking.Main.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:46:51.163193+00:00
-- url     : https://prove2.me/theorems/3a6ae142-b614-4c3b-9640-ab55ddb9bbd3
-- title:
--   Theorem 2.1 — long-cycle-free gain sharing is score-balanced
-- statement:
--   Let $g:[0,1)^2\to(0,1)$ be a gain-sharing rule satisfying complementarity
--
--   $$g(x,y)+g(y,x)=1\qquad(x,y\in[0,1)).$$
--
--   Then the following are equivalent:
--
--   1. $g$ is long-cycle-free on the sampled domain: no finite weighted bipartite residual instance (any finite sides, any set of available pairs, any nonnegative weights), no assignment of ranks in $[0,1)$ and no common total tie order produces a long proposal cycle of Mutual Proposals;
--   2. there is a function $h:[0,1)\to\mathbb R_{>0}$ with
--   $$g(x,y)=\frac{h(y)}{h(x)+h(y)}\qquad(x,y\in[0,1)).$$
--
--   Moreover, the function $h$ in 2 is unique up to multiplication by a positive constant: any two positive functions $h,\tilde h$ that both represent $g$ in this way satisfy $\tilde h=c\,h$ on $[0,1)$ for some $c>0$.
--
--   The theorem singles out the score-balanced rules $g_h$ as exactly those for which Mutual Proposals can never get stuck; it is the design principle behind Harmonic Ranking.
--
--   **Formalization Note** The proposal model is the one of the definition file `Proposals`: available pairs form an arbitrary set $A\subseteq L\times R$ on finite types, weights are nonnegative reals, ranks are the published `Ranks`, and the common tie order is an injective key into $\mathbb N$. The uniqueness clause is stated unconditionally.
--
--   Differences from the source:
--   - generalization: §2.3 fixes a measurable gain-sharing rule → no measurability is assumed on g or h; reason: the statement and long-cycle-freeness are pointwise conditions; every measurable rule is covered, so the theorem specializes to the source's
--   - encoding: g : [0,1)² → (0,1) and h : [0,1) → ℝ>0 → total functions ℝ → ℝ → ℝ and ℝ → ℝ with range, complementarity and positivity hypotheses on [0,1); reason: only values on [0,1) are ever evaluated
--   - encoding: any common total order on potential pairs → an injective key ord : L × R → ℕ, smaller key earlier; reason: every total order on a finite set is induced by such a key and every such key induces one
--   - reading: ties resolved "using the same common total order" → the earliest pair in the order wins; reason: the order is quantified over all total orders, which is closed under reversal, so earliest-wins and latest-wins give the same notion
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 7, Theorem 2.1 (definitions p. 6, Section 2.3)

import Definitions.Def_HarmonicRanking_Main_Supplement_Proposals

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem theorem_2_1 (g : ℝ → ℝ → ℝ)
    (hg : ∀ x ∈ Rank, ∀ y ∈ Rank, 0 < g x y ∧ g x y < 1)
    (hcomp : ∀ x ∈ Rank, ∀ y ∈ Rank, g x y + g y x = 1) :
    (LongCycleFree g ↔
      ∃ h : ℝ → ℝ, (∀ x ∈ Rank, 0 < h x) ∧
        ∀ x ∈ Rank, ∀ y ∈ Rank, g x y = h y / (h x + h y)) ∧
    (∀ h h' : ℝ → ℝ, (∀ x ∈ Rank, 0 < h x) →
      (∀ x ∈ Rank, ∀ y ∈ Rank, g x y = h y / (h x + h y)) →
      (∀ x ∈ Rank, 0 < h' x) →
      (∀ x ∈ Rank, ∀ y ∈ Rank, g x y = h' y / (h' x + h' y)) →
      ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Rank, h' x = c * h x) := by sorry

end HarmonicRanking.Main.Supplement
