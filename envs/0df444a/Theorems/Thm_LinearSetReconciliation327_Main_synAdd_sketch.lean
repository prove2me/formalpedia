-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_synAdd_sketch
-- name    : LinearSetReconciliation327.Main.synAdd_sketch
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T10:05:24.900007+00:00
-- url     : https://prove2.me/theorems/4545e1cc-0e39-47f0-a414-cc540456813f
-- title:
--   Sketch linearity for the HintSketch recursion tree
-- statement:
--   For every CR family and every node of the HintSketch recursion tree, the syntactic sum `Node.synAdd` of the sketches of two sets $a$ and $b$ is the sketch of their symmetric difference: `Node.synAdd T (Node.sketch CR T r a) (Node.sketch CR T r b) = Node.sketch CR T r (symmDiff a b)` — i.e. the sketch map is $\mathbb{F}_2$-linear all the way down the tree, which is what makes the payload `CR x + CR x̂` that `Node.decode` hands a child a legitimate child input.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §5.2 (HintSketch tree recursion and the sketch payload of a child node) and §6 (§9.2 decoder stages: the residual syndrome `CR x + CR x̂`); extracted from the verified development `Solutions/_65_decode_correct.lean` §12.3.

import Definitions.Def_LinearSetReconciliation327_Main_Framework

namespace LinearSetReconciliation327.Main

theorem synAdd_sketch (CR : CRFamily) (T : Node) :
    ∀ (r : Node.Seed T) (a b : Finset ℕ),
      Node.synAdd T (Node.sketch CR T r a) (Node.sketch CR T r b)
        = Node.sketch CR T r (symmDiff a b) := by sorry

end LinearSetReconciliation327.Main
