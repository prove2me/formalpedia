-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_7_4
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:59.521092+00:00
-- url     : https://prove2.me/theorems/c3848e64-2b12-4603-a567-1bb60f1faff4
-- title:
--   Lemma 7.4 (used in the proof of Theorem 1.3) — attachment cut bound
-- statement:
--   Let $Q$ be a simple graph with at least one edge and let $p\ge1$. For every target cut $S$ and every attachment $(i,v,j)$, write $e_{i,v,j}(S)$ for its number of cut edges and $\rho_v^i$ for the number of source neighbors whose same-copy cores lie across the cut from $c_v^i$. Then
--
--   $$e_{i,v,j}(S)\le2(\deg_Q(v)+1)+\rho_v^i.$$
--
--   Equality holds whenever the middle lies on the side of its core and every private vertex of this attachment lies on the other side. This is a sufficient equality condition, with no uniqueness claim when $\rho_v^i=0$. Core-core edges are not part of the attachment. The bound controls every target cut for the optimum and decoding lemma.
--
--   Differences from the source:
--   - encoding: finite vertices and one-based copy and repetition indices → Fin n, Fin 2, and Fin p; dependent private indices; reason: these are bijective renamings, with exactly the source number of vertices and no padding
--   - encoding: cut edges of attachment (i,v,j) → cutCount of the subgraph of actual target edges incident with that attachment; reason: the middle and its private vertices identify the attachment; this excludes core-core edges and counts each edge once
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 7.4, PDF p. 26 (printed p. 25)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Gadget

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 7.4, PDF 26 (printed 25): upper bound for every cut and the full sufficient
equality case, without a uniqueness assertion. -/
theorem lemma_7_4 {n : ℕ} (Q : SimpleGraph (Fin n)) [DecidableRel Q.Adj]
    (p : ℕ) (hm : 1 ≤ Q.edgeFinset.card) (hp : 1 ≤ p)
    (a : Attachment n p) (S : Finset (TargetVertex Q p)) :
    attachmentCut Q p a S ≤ 2 * (Q.degree a.vertex + 1) + crossingDegree Q p a.copy a.vertex S ∧
    (((middle Q p a ∈ S ↔ core Q p a.copy a.vertex ∈ S) ∧
      ∀ t : Fin (Q.degree a.vertex + 1),
        (privateVertex Q p a t ∈ S ↔ core Q p a.copy a.vertex ∉ S)) →
      attachmentCut Q p a S = 2 * (Q.degree a.vertex + 1) +
        crossingDegree Q p a.copy a.vertex S) := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
