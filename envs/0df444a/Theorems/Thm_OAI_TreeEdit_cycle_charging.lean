-- Prove2me | Theorems.Thm_OAI_TreeEdit_cycle_charging
-- name    : OAI.TreeEdit.cycle_charging
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:49:27.82381+00:00
-- url     : https://prove2.me/theorems/26a5d777-97e1-4dc0-b020-61257129b1bb
-- title:
--   Cycle charging: colour-respecting alignments of words made of $T$ cycles leave at least $T\delta/2$ positions unmatched
-- statement:
--   Fix natural numbers $m\ge2$, $B\ge1$, $T$ and $N$. A position $q\in\{0,\dots,TmB-1\}$ of a word of length $TmB$ is viewed as lying in one of $T$ consecutive *cycles* of length $mB$, each made of $m$ consecutive *blocks* of length $B$: position $q$ lies in cycle $\kappa(q)=\lfloor q/(mB)\rfloor\in\{0,\dots,T-1\}$ and has *colour* $\chi(q)=\lfloor q/B\rfloor\bmod m\in\{0,\dots,m-1\}$, the index of its block inside its cycle.
--
--   Let $f,g\colon\{0,\dots,N-1\}\to\{0,\dots,TmB-1\}$ be strictly increasing maps (one may think of an alignment of size $N$ between two such words) that respect colours: $\chi(f(i))=\chi(g(i))$ for every $i<N$. For a cycle $a$ put $S_a=\{i<N:\kappa(f(i))=a\}$. Let $\delta$ be a real number with $\delta\le(m-2)B$, and assume that whenever the indices leaving cycle $a$ under $f$ all land in a single cycle $b$ under $g$, at least $\delta$ positions of cycle $a$ are missed: for all $a,b\in\{0,\dots,T-1\}$,
--   $$\bigl(\kappa(g(i))=b\ \text{ for all } i\in S_a\bigr)\ \Longrightarrow\ \delta\le mB-|S_a|.$$
--   Then
--
--   $$
--   T\,\delta\le 2\,\bigl(TmB-N\bigr).
--   $$
--
--   In words: if matching one cycle into a single cycle always costs at least $\delta$, then the total number $TmB-N$ of unmatched positions is at least $T\delta/2$. The colour condition is what makes splitting a cycle across several target cycles expensive. This is the combinatorial core of the lower bound for the deficit of the cyclically interleaved words that form each level of the tree construction.
--
--   **Formalization Note** $f$ and $g$ are order embeddings `Fin N ↪o Fin (T * (m * B))`, and $\kappa$ is `blockIndex` with block length $mB$. The differences $mB-|S_a|$ and $TmB-N$ are truncated natural-number subtractions cast to $\mathbb R$; both are genuine differences here, because $|S_a|\le mB$ and $N\le TmB$ by injectivity of $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CycleCharging.lean#L161-L206

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

open OAI OAI.TreeEdit
universe u
attribute [local instance] Classical.propDecidable

theorem OAI.TreeEdit.cycle_charging {m B T N : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (f g : Fin N ↪o Fin (T * (m * B)))
    (hc : ∀ i, (f i).val / B % m = (g i).val / B % m)
    (δ : ℝ) (hδ : δ ≤ ((m - 2) * B : ℕ))
    (hsmall : ∀ (a b : Fin T),
      (∀ i ∈ Finset.univ.filter (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a),
        blockIndex (by positivity : 0 < m * B) (g i) = b) →
      δ ≤ ((m * B - (Finset.univ.filter
          (fun i => blockIndex (by positivity : 0 < m * B) (f i) = a)).card : ℕ) : ℝ)) :
    (T : ℝ) * δ ≤ 2 * ((T * (m * B) - N : ℕ) : ℝ) := by sorry
