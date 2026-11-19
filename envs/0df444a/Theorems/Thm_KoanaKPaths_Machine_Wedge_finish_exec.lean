-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Wedge_finish_exec
-- name    : KoanaKPaths.Machine.Wedge.finish_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:09.338439+00:00
-- url     : https://prove2.me/theorems/f722e0f2-1def-4cef-b719-52fc981bceaa
-- title:
--   Reassemble the two blocks of a recursive exterior product
-- statement:
--   Let $z\in\{-1,1\}$ and let integer arrays $X,U$ have equal length. Suppose the recursive wedge state holds $U$ on the result stack, $\operatorname{reverse}X$ and $\operatorname{reverse}L$ on its two saved framed stacks, and the sign $z$ on its saved-vector stack. The finishing program creates the framed result
--   $$
--   L\mathbin{+\!+}\bigl[zX_j-U_j\bigr]_j.
--   $$
--   It restores the saved-array and vector tails, pushes $z$ back onto the live label stack, adds one marker to the dimension counter, and preserves the original input-array tail and all unrelated state. Its exact cost is the declared sum of the signed-array preparation, negation of $U$, coordinatewise addition, array movements and marker operations. This is the reconstruction step in the recursive coordinate algorithm for right exterior multiplication.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WedgeFinish.lean, line 20; source snapshot SHA-256 6731cd02582771d960503342f1efbc5caf62ac1bbb35015b5d4ea140a807d5c1.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Wedge.finish_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (z : Int) (xs lower upper : List.{0} Int)
  (ta tr tc tw tvs : List.{0} NLogN.Item)
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int upper))
  (ha : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A) ta)
  (hr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.R)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int upper) (@List.cons.{0} NLogN.Item NLogN.Item.mark tr)))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.C0)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tc)))
  (hw :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.W0)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int lower))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark tw)))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.VS)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) tvs)),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Wedge.finish s
    (KoanaKPaths.Machine.Wedge.finished s z xs lower upper tr tc tw tvs)
    (KoanaKPaths.Machine.Wedge.finishCost z xs lower upper) := by sorry
