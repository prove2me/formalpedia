-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Balanced_mergeOnes_exec
-- name    : KoanaKPaths.Machine.Balanced.mergeOnes_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:33.140422+00:00
-- url     : https://prove2.me/theorems/a1959668-fca4-405c-b376-1925d6dba1e1
-- title:
--   Merging a run of binary carries in balanced integer summation
-- statement:
--   Suppose a binary-counter stack begins with $m$ integer ones, its following tail is not positive, and the partials stack begins with integers $Y=(y_1,\ldots,y_m)$. Let the carry register begin with $x$. The merge-ones program consumes these ones and partials, prepends $m$ markers to the restoration stack, and updates the carry to
--   $$x+\sum_j y_j.$$
--   Its exact charge is $C(x,[])=30$ and $C(x,y::Y)=\operatorname{addIntCost}(\operatorname{bits}(x)+\operatorname{bits}(y))+64+C(x+y,Y)$. All original tails and unrelated native state are preserved. The routine implements the carry propagation used when inserting one trial numerator into a balanced sum.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/BalancedNative.lean, line 26; source snapshot SHA-256 f34dc4bd9ef48b1a92003176676bd5aad1f473ea3f28f6118d43936d58ec94f5.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Balanced.mergeOnes_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int) (ys : List.{0} Int)
  (bt pt ct : List.{0} NLogN.Item) (hbt : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item bt)) NLogN.Cls.pos)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
          (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        bt))
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) pt))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Carry)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) ct)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.mergeOnes s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits bt)
          KoanaKPaths.Machine.Balanced.Partials pt)
        KoanaKPaths.Machine.Balanced.Carry
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
              (@List.sum.{0} Int Int.instAdd
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) ys)))
          ct))
      KoanaKPaths.Machine.Balanced.Restore
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Restore)))
    (KoanaKPaths.Machine.Balanced.mergeCost x ys) := by sorry
