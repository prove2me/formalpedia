-- Prove2me | Theorems.Thm_HalfIndMatch_proposition_3_1
-- name    : HalfIndMatch.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:11:55.923436+00:00
-- url     : https://prove2.me/theorems/dd1892cc-e479-4fcf-8adb-9295f0662a1b
-- title:
--   Proposition 3.1 — whp every maximal induced matching of $G(n,p)$ has at least $(1/2-\varepsilon)L$ edges
-- statement:
--   Fix $\kappa\in(0,1)$ and $\varepsilon\in(0,1/2)$, and let $b$ and $L$ be as in (1). There is $C=C(\varepsilon,\kappa)>1$ such that, for all sufficiently large $n$ and uniformly over $C/n\le p\le1-\kappa$, for $G\sim G(n,p)$,
--
--   $$\mathbb P\Big[\text{there is a maximal induced matching }M\text{ with }|M|<\Big(\tfrac12-\varepsilon\Big)L\Big]\le L\exp\Big(-\frac{(np)^{2\varepsilon}}{30p}\Big)$$
--
--   and the same probability is at most $\exp(-n^{\varepsilon})$.
--
--   In particular, with high probability every maximal induced matching has at least $(1/2-\varepsilon)L$ edges. Since Greedy always outputs a maximal induced matching, Theorem 2.1 follows.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); edges are Sym2 (Fin n) in G.edgeSet, matchings Finset (Sym2 (Fin n)); reason: relabelling of the vertices; same instances
--   - encoding: G ∼ G(n, p), each pair an edge independently with probability p → the published law LPCommunity.SBMRecovery.erProb n p (edge weights clamp01 p); reason: clamp01 is the identity on [0, 1], which contains every p of the statement
--   - generalization: … = exp(−Ω(n^ε)) → … ≤ exp(−n^ε); reason: the Ω with constant 1; the proof ends with exactly this bound, and it implies the printed asymptotic form
--   - encoding: 'In particular, with high probability every maximal induced matching has at least (1/2 − ε)L edges' → not a separate conjunct; reason: it is the complement of the stated bound, which tends to 0
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), Proposition 3.1, p.13 (PDF p.15); last display of its proof, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_IsInducedMatching
import Definitions.Def_HalfIndMatch_Lval

open LPCommunity.SBMRecovery

namespace HalfIndMatch

/-- Proposition 3.1, p.13: fix `κ ∈ (0, 1)` and `ε ∈ (0, 1/2)`. There is `C = C(ε, κ) > 1` such
that, for all sufficiently large `n` and uniformly over `C/n ≤ p ≤ 1 − κ`, with
`E = {there is a maximal induced matching M with |M| < (1/2 − ε)L}`,
`P[E] ≤ L exp(−(np)^{2ε}/(30p))` and `P[E] ≤ exp(−n^ε)`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), Proposition 3.1, p.13 (PDF p.15); the second bound is the last display of its proof,
p.14 (PDF p.16).

**Formalization Note** The printed "`= exp(−Ω(n^ε))`" is stated as `≤ exp(−n^ε)`, the form the
proof ends with (a constant 1 in the `Ω`). `n^ε` and `(np)^{2ε}` are `Real.rpow`. -/
theorem proposition_3_1 (κ ε : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ, C / n ≤ p → p ≤ 1 - κ →
      erProb n p (fun G => ∃ M : Finset (Sym2 (Fin n)),
          IsMaximalInducedMatching G M ∧ (M.card : ℝ) < (1 / 2 - ε) * Lval n p) ≤
        Lval n p * Real.exp (-(((n : ℝ) * p) ^ (2 * ε) / (30 * p))) ∧
      erProb n p (fun G => ∃ M : Finset (Sym2 (Fin n)),
          IsMaximalInducedMatching G M ∧ (M.card : ℝ) < (1 / 2 - ε) * Lval n p) ≤
        Real.exp (-((n : ℝ) ^ ε)) := by sorry

end HalfIndMatch
