-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_compareLE_exec
-- name    : KoanaKPaths.Machine.compareLE_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:08:12.969115+00:00
-- url     : https://prove2.me/theorems/dc0c6fd6-4d0a-4acf-8839-41a9834efbbd
-- title:
--   Readonly signed-integer comparison on native stacks
-- statement:
--   Let five native registers $i,j,t,w,d$ be pairwise distinct, and suppose the first two begin with arbitrary integers $x,y$. The comparison program preserves both operands and changes only the destination stack:
--   $$d_{\rm after}=\begin{cases}\#::d_{\rm before},&x\le y,\\d_{\rm before},&x>y.\end{cases}$$
--   Its exact bit charge is $\operatorname{compareCost}(x,y)$, comprising the two operand duplications, negation of $y$, addition forming $x-y$, a sign test, and disposal of the temporary difference. The scratch registers return to their original tails; input position and output are preserved. This provides a reusable signed comparison primitive for graph lookup and median counting.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeCompare.lean, line 22; source snapshot SHA-256 ff5018f4604d37998d1e231a1b4837b61eb36db634fe815cd391ccfd6891701f.

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

theorem KoanaKPaths.Machine.compareLE_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (i j tmp work dst : Fin S) (hij : @Ne.{1} (Fin S) i j)
  (hit : @Ne.{1} (Fin S) i tmp) (hiw : @Ne.{1} (Fin S) i work) (hid : @Ne.{1} (Fin S) i dst)
  (hjt : @Ne.{1} (Fin S) j tmp) (hjw : @Ne.{1} (Fin S) j work) (hjd : @Ne.{1} (Fin S) j dst)
  (htw : @Ne.{1} (Fin S) tmp work) (htd : @Ne.{1} (Fin S) tmp dst) (hwd : @Ne.{1} (Fin S) work dst) (s : NLogN.IState S)
  (x y : Int) (li lj : List.{0} NLogN.Item)
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s i) (@List.cons.{0} NLogN.Item (NLogN.Item.int x) li))
  (hy : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s j) (@List.cons.{0} NLogN.Item (NLogN.Item.int y) lj)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.compareLE S i j tmp work dst) s
    (@NLogN.IState.upd S s dst
      (@ite.{1} (List.{0} NLogN.Item) (@LE.le.{0} Int Int.instLEInt x y) (Int.decLe x y)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark (@NLogN.IState.G S s dst)) (@NLogN.IState.G S s dst)))
    (KoanaKPaths.Machine.compareCost x y) := by sorry
