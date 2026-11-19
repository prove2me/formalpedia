-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Balanced_foldPartials_exec
-- name    : KoanaKPaths.Machine.Balanced.foldPartials_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:16.49821+00:00
-- url     : https://prove2.me/theorems/b862ca27-11ff-44d5-aa8a-367df9cf3c91
-- title:
--   Folding balanced partial sums into a native accumulator
-- statement:
--   Let $c_1,\ldots,c_m$ be balanced-summation chunks, with integer values $y_1,\ldots,y_m$. Suppose their values occupy the partials stack above a marker, and the sum register begins with $x$. The partial-fold program consumes those values and replaces the accumulator by
--   $$x+\sum_{j=1}^{m}y_j.$$
--   Its exact native bit charge is $F(x,[]) =30$ and $F(x,y::Y)=\operatorname{addIntCost}(\operatorname{bits}(x)+\operatorname{bits}(y))+30+F(x+y,Y)$, where $\operatorname{bits}$ is the bit length of absolute value. Chunk levels need not be ordered for this final fold. The marker and all unrelated state are preserved. This contract completes balanced accumulation after the carry phase.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/BalancedInsert.lean, line 42; source snapshot SHA-256 47883527cd79b6f9f5c7a8361b43b359ab9c0c7f40f01ac1105ac62be810e834.

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

theorem KoanaKPaths.Machine.Balanced.foldPartials_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int)
  (cs : List.{0} KoanaKPaths.Machine.Balanced.Chunk) (pt st : List.{0} NLogN.Item)
  (ht : @Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item pt)) NLogN.Cls.mark)
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))
        pt))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Sum)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) st)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.foldPartials s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials pt)
      KoanaKPaths.Machine.Balanced.Sum
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
            (@List.sum.{0} Int Int.instAdd
              (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
              (@List.map.{0, 0} (Prod.{0, 0} Nat Int) Int (@Prod.snd.{0, 0} Nat Int) cs))))
        st))
    (KoanaKPaths.Machine.Balanced.foldCharge x cs) := by sorry
