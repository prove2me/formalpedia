-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_1_8
-- name    : HeilmanMax3Cut.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:54.511207+00:00
-- url     : https://prove2.me/theorems/cf42e920-8c48-45b1-88d7-71c0d0ddf2eb
-- title:
--   Theorem 1.8 — sharp UG-hardness of rank-$k$ MAX-CUT within $\alpha_{\mathrm{BOV},k}+\varepsilon$ ($k\ge3$)
-- statement:
--   Let $k\ge3$ and assume the Unique Games Conjecture. Then for every $\varepsilon>0$ it is NP-hard to approximate rank-$k$ MAX-CUT within $\alpha_{\mathrm{BOV},k}+\varepsilon$: there are $c>0$ and $s$ with
--
--   $$\frac sc\le\alpha_{\mathrm{BOV},k}+\varepsilon$$
--
--   such that it is NP-hard to distinguish weighted graphs whose rank-$k$ MAX-CUT value $\max_{v_i\in S^{k-1}}\sum_{\{i,j\}\in E}w_{ij}(1-\langle v_i,v_j\rangle)/2$ is at least $c\,w(G)$ from those whose value is at most $s\,w(G)$. Here $\alpha_{\mathrm{BOV},k}=\inf_{-1<\rho<0}(1-F^*(k,\rho))/(1-\rho)$ is (6).
--
--   The ratio matches that of rank-$k$ Gaussian rounding, so the result is sharp for every $k\ge3$.
--
--   Differences from the source:
--   - reading: the Unique Games Conjecture (paraphrased on p.5 in the linear-equations form) → the published OptInapprox.MaxCut.UGC (Khot's Unique Label Cover form); reason: the paper cites the conjecture of [Kho02, KN10], stated there for Unique Label Cover; the same reading as the published goal HeilmanMax3Cut.theorem_1_4
--   - reading: the rank-k MAX-CUT problem (named, not restated in the paper) → rankCutVal k: the maximum over unit vectors v_i ∈ ℝᵏ of Σ_edges (1 − ⟨v_i, v_j⟩)/2; reason: the problem of [BOV14] and [HNP+23], to which the paper refers; α_BOV,k in (6) is the ratio of its rank-k Gaussian rounding
--   - encoding: NP-hard to approximate the rank-k MAX-CUT problem within α_BOV,k + ε → ∃ c > 0, s with s/c ≤ α_BOV,k + ε and (c, s)-gap NP-hardness (ValGapHard), both promise sets restricted to graphs with at least one edge; reason: (c, s)-hardness implies NP-hardness of approximation within s/c, as in the published goal; the clause 0 < w(G) only excludes the edgeless graph, on which both promises hold
--   - generalization: weights w : [n]² → [0, ∞), w_ij = w_ji, w_ii = 0 → natural-number weights given by a loopless edge list with multiplicities (OptInapprox.MaxCut.WMaxCut); reason: hardness on this subclass of instances implies hardness on all nonnegative weights (the identity map is a reduction), so the statement implies the paper's
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.8, p.6 (proof p.20)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_Supplement_alphaBOV
import Definitions.Def_HeilmanMax3Cut_Supplement_rankCutVal
import Definitions.Def_HeilmanMax3Cut_Supplement_ValGapHard
open OptInapprox.MaxCut

namespace HeilmanMax3Cut.Supplement

/-- **Theorem 1.8 (Sharp Hardness for rank-`k` MAX-CUT).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.8, p.6: "Let `k ≥ 3`.
Assume the Unique Games Conjecture. Then, for any `ε > 0`, it is NP-hard to approximate the rank-`k`
MAX-CUT problem within a multiplicative factor `α_BOV,k + ε`," with `α_BOV,k` from (6), p.10.

**Formalization Note.** The UGC is the published `OptInapprox.MaxCut.UGC`; the rank-`k` value is
`rankCutVal k` ([BOV14]/[HNP+23]); "NP-hard to approximate within `r`" is the `(c, s)`-gap encoding
`ValGapHard` of the published goal `HeilmanMax3Cut.theorem_1_4`. Instances are ℕ-weighted graphs
(`WMaxCut`), a subclass of nonnegative real weights. -/
theorem theorem_1_8 (k : ℕ) (hk : 3 ≤ k) (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ alphaBOV k + ε ∧
      ValGapHard (rankCutVal k) c s := by sorry

end HeilmanMax3Cut.Supplement
