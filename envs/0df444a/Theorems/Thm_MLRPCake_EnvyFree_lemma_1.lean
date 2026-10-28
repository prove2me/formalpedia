-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_lemma_1
-- name    : MLRPCake.EnvyFree.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:16.017114+00:00
-- url     : https://prove2.me/theorems/da235837-b6bb-4117-b34b-86df450ff1a6
-- title:
--   Lemma 1, p. 9 — MLRP densities: interval value ratios increase to the right, normalized tail values dominate
-- statement:
--   Let $f_i$ and $f_j$ be two value densities on $[0,1]$ (nonnegative, bounded, integrable, total value $1$) that are strictly positive on $[0,1]$ and bear the monotone likelihood ratio property in this order:
--   $$\frac{f_j(b)}{f_i(b)}\le\frac{f_j(c)}{f_i(c)}\qquad\text{for all }0\le b\le c\le 1.$$
--   Then the following hold.
--
--   1. For all intervals $[a,b],[c,d]\subseteq[0,1]$ with $b\le c$ (and $c<d$),
--   $$\frac{\int_a^b f_j}{\int_a^b f_i}\le\frac{\int_c^d f_j}{\int_c^d f_i}.$$
--   2. For every interval $[a,b]\subseteq[0,1]$ and every $x\in[a,b]$,
--   $$\frac{\int_x^b f_i}{\int_a^b f_i}\le\frac{\int_x^b f_j}{\int_a^b f_j}.$$
--
--   In terms of valuations, (i) says $v_j(a,b)/v_i(a,b)\le v_j(c,d)/v_i(c,d)$: the relative value of agent $j$ grows from left to right. (ii) says that over any interval, agent $j$'s normalized values stochastically dominate agent $i$'s. This is the tool behind the envy-freeness of ripple divisions (Theorem 6).
--
--   **Formalization Note** In (i) the right-hand interval is required to be nondegenerate ($c<d$). The page's fraction presupposes this, and in Lean $x/0=0$ would make the right side $0$ for $c=d$. Degenerate intervals elsewhere ($a=b$) make both sides of the inequality $0$ and are harmless. The paper's further remark that (i) and (ii) are equivalent (p. 10) is not part of this statement.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 9, Lemma 1 (i)–(ii) (proof in Appendix A.1, pp. 26–27)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Lemma 1, p. 9: two value densities bearing MLRP (strictly positive, `f_j/f_i` nondecreasing
on `[0,1]`) satisfy (i) interval value ratios increase from left to right and (ii) normalized
right-tail values of `f_j` dominate those of `f_i`. The nondegeneracy `c < d` in (i) is added
because Lean's `x / 0 = 0`. -/
theorem lemma_1 (fi fj : ℝ → ℝ) (hi : IsDensity fi) (hj : IsDensity fj)
    (hpos_i : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fi x) (hpos_j : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fj x)
    (hmlrp : ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ 1 → fj b / fi b ≤ fj c / fi c) :
    (∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c < d → d ≤ 1 →
      (∫ t in a..b, fj t) / (∫ t in a..b, fi t) ≤ (∫ t in c..d, fj t) / (∫ t in c..d, fi t)) ∧
    (∀ a x b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 →
      (∫ t in x..b, fi t) / (∫ t in a..b, fi t) ≤ (∫ t in x..b, fj t) / (∫ t in a..b, fj t)) := by sorry

end MLRPCake.EnvyFree
