-- Prove2me | Theorems.Thm_OnlineCAP_lemma_4_9
-- name    : OnlineCAP.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:08.493894+00:00
-- url     : https://prove2.me/theorems/1039e451-768f-40cb-985b-702e27c4bd8a
-- title:
--   Lemma 4.9 — the queries of Algorithm 2 are heavy: |Q_t| ≥ ⌈n/2⌉ and Q_t ⊆ A_t(R_t)
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a finite point set with $n=|P|$, $x\ge0$ a fractional vector on $P$, and $R\subseteq P$ a request with $x(R)\ge1$. The query $Q$ that Algorithm 2 sends to the sampler satisfies
--   $$|Q|\ge B=\lceil n/2\rceil,\qquad Q\subseteq A(R),$$
--   and hence $\pi(e)\in R$ for every $e\in Q$: purchasing the physical parent of any sampled copy hits the request.
--
--   Differences from the source:
--   - generalization: a request R_t (a bottomless rectangle) with the current fractional solution → every R ⊆ P with x(R) ≥ 1 and every x ≥ 0; reason: the argument uses only x(R) ≥ 1 (Lemma 4.5) and the split at the range-tree node
--   - reading: the deepest node v of the range tree containing [a_t, b_t] (w.l.o.g. a_t, b_t x-coordinates of points of P) → the deepest node containing the x-ranks of the points of R ∩ P; reason: the same w.l.o.g. as p.17 (shrinking [a_t, b_t] to the x-range of R ∩ P does not change R ∩ P); the algorithm sees R ∩ P, and the node's children still split A(R)
--   - encoding: ties in arg max{|A_left|, |A_right|} → the left piece; reason: the source leaves ties unspecified and the lemma holds for either choice
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Lemma 4.9, p.20

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_zvec
import Definitions.Def_OnlineCAP_acount
import Definitions.Def_OnlineCAP_active
import Definitions.Def_OnlineCAP_activeOn
import Definitions.Def_OnlineCAP_xrank
import Definitions.Def_OnlineCAP_nodeSet
import Definitions.Def_OnlineCAP_query

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Lemma 4.9 (Heaviness).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Lemma 4.9, p.20 (PDF p.20): "For any request Rt, the query set
Qt produced by Algorithm 2 satisfies |Qt| ≥ B. Furthermore, Qt ⊆ At(Rt), so for any e ∈ Qt, the
point π(e) ∈ P ∩ Rt, and purchasing π(e) hits the request Rt." Here `B = ⌈n/2⌉` (Algorithm 2,
p.18).

Let `P` be a finite point set with `n = |P|`, `x ≥ 0` a vector on `P` and `R ⊆ P` a request with
`x(R) ≥ 1`. The query `Q` of Algorithm 2 satisfies `|Q| ≥ ⌈n/2⌉`, `Q ⊆ A(R)`, and `π(e) ∈ R` for
every `e ∈ Q`.

**Formalization Note.** `R` is the trace `R_t ∩ P` of the request on `P`, and ranges over all
subsets of `P` (the argument does not use the bottomless shape). The query locates its range-tree
node from the x-ranks of the points of `R` (see `query`). -/
theorem lemma_4_9 (P : Finset (ℝ × ℝ)) (x : ↥P → ℝ) (hx : ∀ p, 0 ≤ x p) (R : Set ↥P)
    (hR : 1 ≤ ∑ p, R.indicator x p) :
    ⌈(P.card : ℝ) / 2⌉₊ ≤ (query P x R).card ∧ query P x R ⊆ activeOn P x R ∧
      ∀ e ∈ query P x R, e.1 ∈ R := by sorry

end OnlineCAP
