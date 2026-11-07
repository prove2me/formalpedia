-- Prove2me | Theorems.Thm_MetricMSO_lemma_4_2
-- name    : MetricMSO.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:22.18031+00:00
-- url     : https://prove2.me/theorems/a55c74be-c34d-4944-a350-b83079d6c00d
-- title:
--   Lemma 4.2 — finite certificate for equal arcs on an isometric cycle
-- statement:
--   Let $G[C]$ be an isometric cycle, $P$ an $s$-$t$ arc and $Q$ a $u$-$v$ arc of $C$, and let $N$ be an integer with $N>4$ and $N>2\,\mathrm{cbl}(G)$. Then $|E(P)|=|E(Q)|$ if and only if there are $\eta\in\{+,-\}$ and a map $c:V(G)\to\mathbb Z_N$ such that
--
--   1. for every oriented edge $(r,z)$ of $G$, the residue $c(z)-c(r)$ has an integer representative in $\{-2,-1,0,1,2\}$, and
--   2. for every oriented edge $(r,z)$ of $G[C]$, we have $c(z)-c(r)\equiv\beta^\eta_{P,Q}(r,z)\pmod N$.
--
--   Differences from the source:
--   - encoding: an oriented edge (r, z) of G[C] → adjacent r, z in G with r, z ∈ C; reason: G[C] is the induced subgraph
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 4.2, p.26 (PDF 28)

import Mathlib
import Definitions.Def_MetricMSO_EqGC
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_arcBeta

namespace MetricMSO

/-- **Lemma 4.2.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.26 (PDF 28): "Suppose that G[C] is an
isometric cycle, and let P be an s-t arc and Q a u-v arc of C. Let N be an integer with N > 4 and
N > 2 cbl(G). Then |E(P)| = |E(Q)| if and only if there exist η ∈ {+, −} and a map c: V(G) → ZN
satisfying the following conditions. (i) For every oriented edge (r, z) of G, the residue c(z) − c(r)
has an integer representative in {−2, −1, 0, 1, 2}. (ii) For every oriented edge (r, z) of G[C], we
have c(z) − c(r) ≡ β^η_{P,Q}(r, z) (mod N)."

**Formalization Note** `η = true` is `+`. An oriented edge is an ordered pair of adjacent vertices. -/
theorem lemma_4_2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (C : Finset V)
    (hC : IsGeodesicCycleSet G C) {s t u v : V} (P : G.Walk s t) (Q : G.Walk u v)
    (hP : IsArc C P) (hQ : IsArc C Q) (N : ℕ) (hN : 4 < N) (hcbl : 2 * cbl G < N) :
    P.length = Q.length ↔ ∃ (η : Bool) (c : V → ZMod N),
      (∀ r z, G.Adj r z → ∃ j : ℤ, j ∈ ({-2, -1, 0, 1, 2} : Set ℤ) ∧ c z - c r = (j : ZMod N)) ∧
      (∀ r ∈ C, ∀ z ∈ C, G.Adj r z → c z - c r = ((arcBeta η P Q r z : ℤ) : ZMod N)) := by sorry

end MetricMSO
