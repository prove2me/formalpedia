-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_Supplement_lemma_3_2
-- name    : OnlineMaxWeightMatch.Approx.Supplement.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:26:08.217805+00:00
-- url     : https://prove2.me/theorems/c1dc9e9c-212d-4dc1-834a-a7e4969dc747
-- title:
--   Lemma 3.2, p. 6 — the split formula satisfies $OPT_{on}(\phi')=OPT_{on}(\phi)+E_n$
-- statement:
--   Let $\phi$ be a 3CNF MAX-SSAT formula with variables $x_1,\dots,x_n$, and for each deterministic variable $x_i$ let $G_i$ be a graph of expansion at least $1$ on the $a(i)$ occurrences of $x_i$. Let $\phi'$ be the split formula of §3.1, in which the occurrences of $x_i$ become copies $x_{i,1},\dots,x_{i,a(i)}$ and every edge of $G_i$ adds the two clauses (2). Let
--   $$E_n=\sum_{\text{odd } i\le n}2\,|E(G_i)|.$$
--   Then
--   $$OPT_{on}(\phi')=OPT_{on}(\phi)+E_n.$$
--
--   The identity is exact. It is the step of the proof of Lemma 3.1 that lets an approximation of $OPT_{on}(\phi')$ be translated into one of $OPT_{on}(\phi)$.
--
--   Differences from the source:
--
--   - generalization: φ as in Lemma 2.3 (no negated random variable, random variables in at most k clauses) → any 3CNF formula φ; reason: the proof of the identity uses neither property; the formulas of Lemma 2.3 are a special case
--   - generalization: G_i from Lemma 2.4: expansion at least 1 and maximum degree at most d → any graphs G_i with expansion at least 1; reason: the proof uses only the expansion; the degree bound matters for the occurrence bound of Lemma 3.1, and the graphs of Lemma 2.4 are a special case
--   - reading: "the order of variables x_{i,j} and x_i in φ is some arbitrary order …; by adding dummy random variables …" → the copies of x_i form one block x_{i,1}, y, x_{i,2}, y, …, x_{i,a(i)} with fresh dummy random variables y, in the position of x_i; a deterministic variable with no occurrence stays as one unused variable; reason: the paper leaves the layout unspecified; this is one layout with the required properties (block order kept, deterministic copies stay deterministic)
--   - reading: x_i "appears in a(i) clauses" and its j-th occurrence is replaced → a(i) is the number of occurrences of x_i (literal positions), each replaced by its own copy; reason: each occurrence needs its own copy; the two counts agree unless a clause repeats a variable
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 6, Lemma 3.2 (construction §3.1, pp. 6–7)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ExpanderSplit

namespace OnlineMaxWeightMatch.Approx.Supplement

/-- Lemma 3.2: for a 3CNF MAX-SSAT formula `φ` and graphs `G v` of expansion at least 1 on the
copies of each deterministic variable, the split formula `φ′` satisfies
`OPT_on(φ′) = OPT_on(φ) + E_n`. -/
theorem lemma_3_2 (φ : SSATFormula) (hφ : φ.IsThreeCNF)
    (G : (v : ℕ) → SimpleGraph (Fin (φ.occ v)))
    (hG : ∀ v, v < φ.n → ¬ IsRandomVar v → HasExpansionAtLeastOne (G v)) :
    ssatOpt (φ.split G) = ssatOpt φ + φ.En G := by sorry

end OnlineMaxWeightMatch.Approx.Supplement
