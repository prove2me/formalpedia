-- Prove2me | Theorems.Thm_HZTractability_lemma_A_3
-- name    : HZTractability.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:13:51.889182+00:00
-- url     : https://prove2.me/theorems/370e2111-c873-4eab-8286-e3edb488968c
-- title:
--   Lemma A.3 — balancing goods: $N>G_{\mathrm{listed}}$
-- statement:
--   Under the standing assumptions of Appendix A, let $G$ be a nonempty directed graph satisfying (2). The number $N$ of buyers of $M(G;a,\tau,K)$ exceeds the number $G_{\mathrm{listed}}$ of goods in the five groups per vertex:
--   $$
--   N>G_{\mathrm{listed}} .
--   $$
--   Hence the balancing group $Z$ is nonempty, and the completed market has the same number of buyers and goods.
--
--   Differences from the source:
--   - encoding: $N$, $G_{\mathrm{listed}}$ and the completed market → the cardinalities of the structured buyer and good types; $Z$ has $N-G_{\mathrm{listed}}$ goods in natural subtraction; reason: same numbers; the first conjunct makes the subtraction exact
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma A.3, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_HZTractability_kappa
import Definitions.Def_HZTractability_admissible
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_Market

namespace HZTractability

/-- **Lemma A.3 (Balancing goods)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, p.37 (PDF 39)): "For a nonempty graph, N > G_listed. Hence the balancing
group Z is nonempty, and the completed market has the same number of buyers and goods."

For a nonempty graph `G` satisfying (2) and the standing parameters of Appendix A, the number `N`
of buyers of `M(G; a, τ, K)` exceeds the number `G_listed` of goods in the five groups per vertex,
and the market has as many goods as buyers.

**Formalization Note** `N` is the cardinality of the buyer type; the balancing group has
`N − G_listed` goods, so `N > G_listed` says it is nonempty. -/
theorem lemma_A_3 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) (τ : ℚ) (hτ0 : 0 < τ)
    (hτ1 : τ ≤ kappa / 100) (K : ℕ) (hK : admissible a K) (G : ThrGraph) (hn : 1 ≤ G.n)
    (hG : G.Cond2) :
    Glisted a τ K G < Fintype.card (Buyer a τ K G) ∧
      Fintype.card (Buyer a τ K G) = Fintype.card (Good a τ K G) := by sorry

end HZTractability
