-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_flow_3_7
-- name    : IIDMultiItem.TwoPoint.flow_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:58:49.788132+00:00
-- url     : https://prove2.me/theorems/ee294efe-a3ec-41a1-b758-b40306cdc8c0
-- title:
--   §3.3 flow (3.7) — the weights (a)–(c) form a flow; virtual values b on reported-high items, ϕ_{d−r,r} on D \ T, at most a on H \ Q
-- statement:
--   Let $0<a<b$, $0<p<1$, and let $H\subseteq[m]$ be the set of items some opponent reports high, $D=[m]\setminus H$, $d=|D|$. The weights $\lambda$ of (3.7) and §B.2 rules (a)–(c) (definition `countFlow`) are a flow for the two-point type space: all weights are nonnegative and conservation (2.4) holds at every report. For every report $S=Q\cup T$ ($Q=S\cap H$, $T=S\cap D$, $r=|T|$) and item $j$, the virtual value (2.6) satisfies
--   $$\Phi_j(S)=b\ \ (j\in S),\qquad \Phi_j(S)=\phi_{c,r}\ \text{with } c=d-r\ \ (j\in D\setminus T),\qquad \Phi_j(S)\le a\ \ (j\in H\setminus Q).$$
--   The source states this as: "All weights are nonnegative; conservation is verified in Section B.2. By (2.6), an item that buyer i reports high has virtual value b; for j ∈ D \ T, (3.7) gives Φ_j(S) = ϕ_{c,r} with c = d − r; and for j ∈ H \ Q, Φ_j(S) ≤ a."
--
--   On $D$ this is the one-dimensional Myerson flow on counts; it is the flow that Lemma 3.4 feeds into Corollary 2.4.
--
--   Differences from the source:
--   - encoding: the flow chosen for buyer i and reports v_{-i} → countFlow p m H for an arbitrary set H ⊆ [m] (the items opponents report high); reason: the source notes the flow depends on (i, v_{-i}) only through H; every H arises (H = ∅ when n = 1, any H when n ≥ 2)
--   - encoding: rule (b), processing Q in decreasing order of cardinality → λ(Q, Q \ {j}) = mass Q / |Q| with mass Q = f_H(Q) + ∑_{j' ∈ H \ Q} λ(Q ∪ {j'}, Q), by recursion on |H \ Q|; reason: the same weights, computed by the same recursion
--   - generalization: m ≥ 1 (§2.1: items [m] for a positive integer m) → any m ∈ ℕ; reason: at m = 0 the only type is ∅, with f(∅) = 1 = λ(∅, ⊥), and there are no items; for m ≥ 1 it is the paper's statement
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 15 (PDF 17), §3.3 (after (3.7)); pp. 37–38 (PDF 39–40), §B.2

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Flow
import Definitions.Def_IIDMultiItem_TwoPoint_Counts
import Definitions.Def_IIDMultiItem_TwoPoint_CountFlow

namespace IIDMultiItem.TwoPoint

/-- §3.3 / §B.2: for every set `H` of items reported high by the opponents, the weights (3.7),
(a)–(c) are a flow for the two-point type space, and its virtual values are `b` on the items the
buyer reports high, `ϕ_{c,r}` with `c = d − r` on `j ∈ D \ T` (`d = |D|`, `r = |T|`, `T = S \ H`),
and at most `a` on `j ∈ H \ Q`. -/
theorem flow_3_7 (a b p : ℝ) (ha : 0 < a) (hab : a < b) (hp0 : 0 < p) (hp1 : p < 1)
    (m : ℕ) (H : Finset (Fin m)) :
    (countFlow p m H).IsFlow (twoPoint a b p m) ∧
    ∀ (S : Finset (Fin m)) (j : Fin m),
      (j ∈ S → (countFlow p m H).virtualValue (twoPoint a b p m) S j = b) ∧
      (j ∉ S → j ∉ H → (countFlow p m H).virtualValue (twoPoint a b p m) S j =
        phi a b p ((Finset.univ \ H).card - (S \ H).card) (S \ H).card) ∧
      (j ∉ S → j ∈ H → (countFlow p m H).virtualValue (twoPoint a b p m) S j ≤ a) := by sorry

end IIDMultiItem.TwoPoint
