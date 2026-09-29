-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_relabel_only_when_applicable
-- name    : GoldbergTarjan.FIFO.relabel_only_when_applicable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:34:25.014522+00:00
-- url     : https://prove2.me/theorems/ddd0b570-9a2f-415b-ade8-d702c7fcac1c
-- title:
--   Lemma 4.1 — the push/relabel operation relabels only when relabeling is applicable
-- statement:
--   Consider a run of the first-in, first-out algorithm on a flow network. Take any discharge of the run, say of vertex $v$, and any push/relabel$(v)$ operation inside it that takes the relabeling branch of Fig. 3: no push is applicable through the current edge of $v$, and that edge is the last one on the edge list of $v$. Then, at that moment, the relabeling operation of Fig. 1 is applicable to $v$: $$v \text{ is active and } \; d(v) \le d(w) \ \text{ for every } w \text{ with } r_f(v,w) > 0.$$
--
--   Thus the implementation with current edges performs only legitimate relabelings, and every run of the FIFO algorithm is a run of the generic push–relabel algorithm.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 929, Lemma 4.1

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 4.1 (Goldberg–Tarjan 1988, p. 929): the push/relabel operation does a relabeling only
when the relabeling operation is applicable. In every run of the first-in, first-out algorithm,
whenever the `j`-th push/relabel operation of the `k`-th discharge (of the front vertex `v`)
takes the relabeling branch of Fig. 3, `relabel(v)` is applicable (Fig. 1) at that moment. -/
theorem relabel_only_when_applicable {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) (k : ℕ) (hk : k < K) (j : ℕ) (hj : j < J k)
    (hrel : IsRelabelOp N L (frontVertex N (S k))
      (prIter N L (frontVertex N (S k)) (S k).cfg j)) :
    RelabelApplicable N (prIter N L (frontVertex N (S k)) (S k).cfg j).f
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d (frontVertex N (S k)) := by sorry

end GoldbergTarjan.FIFO
