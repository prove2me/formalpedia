-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_1_7
-- name    : HeilmanMax3Cut.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:08:08.905449+00:00
-- url     : https://prove2.me/theorems/53278ce1-91d9-429f-b138-c70caf4a7465
-- title:
--   Theorem 1.7 — sharp UG-hardness of product-state Quantum MAX-CUT within $\alpha_{\mathrm{BOV}}+\varepsilon$
-- statement:
--   Assume the Unique Games Conjecture. Then for every $\varepsilon>0$ it is NP-hard to approximate the product-state Quantum MAX-CUT problem within $\alpha_{\mathrm{BOV}}+\varepsilon$: there are $c>0$ and $s$ with
--
--   $$\frac sc\le\alpha_{\mathrm{BOV}}+\varepsilon$$
--
--   such that it is NP-hard to distinguish weighted graphs whose product-state Quantum MAX-CUT value is at least $c\,w(G)$ from those whose value is at most $s\,w(G)$. Here $\alpha_{\mathrm{BOV}}=\alpha_{\mathrm{BOV},3}=0.9563372685\ldots$ is the constant (6) at $k=3$.
--
--   Since the Briët–Oliveira–Vallentin algorithm achieves $\alpha_{\mathrm{BOV}}$ in polynomial time, the theorem determines the approximability threshold of product-state Quantum MAX-CUT under the Unique Games Conjecture.
--
--   Differences from the source:
--   - reading: the Unique Games Conjecture (paraphrased on p.5 in the linear-equations form) → the published OptInapprox.MaxCut.UGC (Khot's Unique Label Cover form); reason: the paper cites the conjecture of [Kho02, KN10], stated there for Unique Label Cover; the same reading as the published goal HeilmanMax3Cut.theorem_1_4
--   - reading: α_BOV := 0.9563372685… (p.5) → alphaBOV 3, the infimum (6) at k = 3; reason: p.10 identifies α_BOV with α_BOV,3 ('when k = 3 … α_BOV,3 = 0.9563372685…'); the decimal is a truncation of that infimum
--   - encoding: NP-hard to approximate the product state Quantum MAX-CUT problem within α_BOV + ε → ∃ c > 0, s with s/c ≤ α_BOV + ε and (c, s)-gap NP-hardness (ValGapHard), both promise sets restricted to graphs with at least one edge; reason: (c, s)-hardness implies NP-hardness of approximation within s/c, as in the published goal; the clause 0 < w(G) only excludes the edgeless graph, on which both promises hold
--   - generalization: weights w : [n]² → [0, ∞), w_ij = w_ji, w_ii = 0 → natural-number weights given by a loopless edge list with multiplicities (OptInapprox.MaxCut.WMaxCut); reason: hardness on this subclass of instances implies hardness on all nonnegative weights (the identity map is a reduction), so the statement implies the paper's
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.7, p.6 (problem p.10; proof p.10)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_Supplement_alphaBOV
import Definitions.Def_HeilmanMax3Cut_Supplement_prodQMCVal
import Definitions.Def_HeilmanMax3Cut_Supplement_ValGapHard
open OptInapprox.MaxCut

namespace HeilmanMax3Cut.Supplement

/-- **Theorem 1.7 (Sharp Hardness for Product State Quantum MAX-CUT).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.7, p.6:
"Assume the Unique Games Conjecture. Then, for any `ε > 0`, it is NP-hard to approximate the product
state Quantum MAX-CUT problem within a multiplicative factor `α_BOV + ε`." Here
`α_BOV = α_BOV,3 = 0.9563372685…` (p.5, and (6) on p.10) and the problem is the one of p.10
(`prodQMCVal`).

**Formalization Note.** The UGC is the published `OptInapprox.MaxCut.UGC`. "NP-hard to approximate
within `r`" is: there are `c > 0` and `s` with `s/c ≤ r` such that it is NP-hard to distinguish
weighted graphs with value `≥ c·w(G)` from those with value `≤ s·w(G)` (`ValGapHard`), as in the
published goal `HeilmanMax3Cut.theorem_1_4`. Instances are ℕ-weighted graphs (`WMaxCut`), a subclass
of the paper's nonnegative real weights; hardness on the subclass implies it on the class. -/
theorem theorem_1_7 (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ alphaBOV 3 + ε ∧
      ValGapHard prodQMCVal c s := by sorry

end HeilmanMax3Cut.Supplement
