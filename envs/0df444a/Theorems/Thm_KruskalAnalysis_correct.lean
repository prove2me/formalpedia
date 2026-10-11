-- Prove2me | Theorems.Thm_KruskalAnalysis_correct
-- name    : KruskalAnalysis.correct
-- status  : Proved
-- author  : @lunjia
-- created : 2026-10-11T00:06:59.786731+00:00
-- url     : https://prove2.me/theorems/fca7ef6e-da23-4ebd-a158-cef7dba5f868
-- title:
--   Kruskal: correctness of every returned minimum spanning forest
-- statement:
--   For mathematical integer-indexed endpoint and weight sequences, assume nonnegative vertex/edge counts and endpoints in range. Every output admitted by `kruskal.Returns` selects a minimum spanning forest: `selectedEdges` reads exactly the flags at the finite input edge identifiers. Weights may be negative, components may be disconnected, and parallel edges or loops are allowed.
--
--   This is the ordinary-value view of the reusable heap-based call theorem. The assertion is conditional on a returned output; the companion call theorem separately proves termination and provides fresh storage and runtime guarantees.
--
--   Part of the [Algo2Lean](https://www.algo2lean.com/) CLRS series: *Introduction to Algorithms*, fourth edition, Chapter 21, §21.2 (Kruskal), the safe-edge principle in Theorem 21.1 (§21.1), and the union-by-rank/path-compression bound in Theorem 19.14 (§19.4).
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/examples/kruskal/analysis/kruskal.lean#L251-L261

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_call_complete

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

theorem KruskalAnalysis.correct :
    ∀ {size count : Int} {sources targets weights chosen : Algo2LeanGenerated.Seq},
      KruskalInput.WellFormed size count sources targets →
        Algo.kruskal.kruskal.Returns
            (Prod.mk.{0, 0} size
              (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
            chosen →
          Algo2Lean.Kruskal.MinimumSpanningForest (KruskalInput.edges sources targets weights count)
            (KruskalAnalysis.selectedEdges sources targets weights chosen count) := by
  sorry
