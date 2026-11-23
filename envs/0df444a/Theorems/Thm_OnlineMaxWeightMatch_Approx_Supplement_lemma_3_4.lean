-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_Supplement_lemma_3_4
-- name    : OnlineMaxWeightMatch.Approx.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:27:28.642812+00:00
-- url     : https://prove2.me/theorems/88b8ed09-e8e1-4907-9e4b-91bacd0d0b69
-- title:
--   Lemma 3.4, p. 8 — every optimal online algorithm on $\mathcal I_\phi$ matches every arriving literal ball
-- statement:
--   Let $\phi$ be a 3CNF MAX-SSAT formula with $n$ variables and $m$ clauses, in which no random variable appears negated and every variable appears in at most $k$ clauses, and let $\mathcal I_\phi$ be the RideHail instance of §3.2. Let $\pi$ be an optimal online algorithm on $\mathcal I_\phi$, that is, a non-anticipating policy whose expected profit equals $OPT_{on}(\mathcal I_\phi)$. Then $\pi$ matches all arriving literal balls: for every arrival pattern of positive probability and every literal ball $t\le n$ that arrives, $\pi$ matches $t$ to one of its neighbouring bins.
--
--   Consequently $OPT_{on}$ earns, from the literal balls, exactly the expected number of arriving literal balls, and its choices for the literal balls define a strategy for $\phi$. Lemma 3.5 relies on this correspondence.
--
--   **Formalization Note** In the RideHail model a non-edge is an edge of weight $0$, so "matched to a neighbouring bin" is stated as "matched to a bin of positive weight". The statement covers every optimal deterministic policy.
--
--   Differences from the source:
--
--   - generalization: φ as in Lemma 3.1 with its constant k → any 3CNF φ with no negated random variable and every variable in at most k clauses, for any k used as the gadget parameter; reason: the lemma is stated for the instances and the constant of Lemma 3.1; it holds for every such k
--   - generalization: "without loss of generality, suppose n is even" → any number n of variables; reason: the construction and the argument do not use the parity of n; even n is a special case
--   - reading: "Algorithm OPT_on matches all arriving literal balls" → every optimal deterministic policy, on every arrival pattern of positive probability, matches every arriving literal ball to a bin of positive weight; reason: the claim is about optimal online algorithms; histories of probability 0 do not affect the value, and in the RideHail model a match through a non-edge (weight 0) is possible and is not a match along an edge
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 8, Lemma 3.4 (construction §3.2, pp. 7–8)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_Gadget

namespace OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx

/-- Lemma 3.4: every optimal online policy on `I_φ` matches every arriving literal ball to one of
its neighbouring bins, on every arrival pattern of positive probability. -/
theorem lemma_3_4 (φ : SSATFormula) (k : ℕ) (hφ : φ.IsThreeCNF) (h1 : φ.NoNegatedRandom)
    (h2 : φ.OccursAtMost k)
    (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
    (hπ : policyValue (gadget φ k) π = optOn (gadget φ k))
    (a : Fin (φ.n + φ.clauses.length) → Bool) (ha : 0 < arrivalProb (gadget φ k) a)
    (t : Fin (φ.n + φ.clauses.length)) (ht : t.val < φ.n) (hat : a t = true) :
    ∃ i, (i, t) ∈ π.matching a ∧ 0 < (gadget φ k).w i t := by sorry

end OnlineMaxWeightMatch.Approx.Supplement
