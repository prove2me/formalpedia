-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_compareEq_exec
-- name    : KoanaKPaths.Machine.compareEq_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:09:34.859612+00:00
-- url     : https://prove2.me/theorems/92b710f6-bd62-41ae-9fd3-ef8afcf27b96
-- title:
--   Preserving equality test for two native signed integers
-- statement:
--   Let five native registers be pairwise distinct: two input registers, two temporary registers and a flag destination. Suppose the input heads are arbitrary signed integers $x,y$. The equality program preserves both integers and every scratch tail, and prepends a marker to the destination precisely when
--   $$
--   x=y.
--   $$
--   If they differ, the destination is unchanged. Its exact charge is
--   $$
--   D(\beta x)+17+D(\beta y)+17+20+A(\beta x+\beta(-y))+26+2\beta(x-y)+2,
--   $$
--   where $\beta$ is integer width, $D$ is the primitive integer-duplication charge and $A$ is the primitive integer-addition charge. All other state components are preserved. This comparison primitive allows graph-record tests to retain their original encoded endpoints for later database restoration.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeEqual.lean, line 16; source snapshot SHA-256 915d586fcb9f0c1aec0f35db8903bfef658471219c4dfdf46c6805633e5c285e.

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

theorem KoanaKPaths.Machine.compareEq_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (i j tmp work dst : Fin S) (hij : @Ne.{1} (Fin S) i j)
  (hit : @Ne.{1} (Fin S) i tmp) (hiw : @Ne.{1} (Fin S) i work) (hid : @Ne.{1} (Fin S) i dst)
  (hjt : @Ne.{1} (Fin S) j tmp) (hjw : @Ne.{1} (Fin S) j work) (hjd : @Ne.{1} (Fin S) j dst)
  (htw : @Ne.{1} (Fin S) tmp work) (htd : @Ne.{1} (Fin S) tmp dst) (hwd : @Ne.{1} (Fin S) work dst) (s : NLogN.IState S)
  (x y : Int) (li lj : List.{0} NLogN.Item)
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s i) (@List.cons.{0} NLogN.Item (NLogN.Item.int x) li))
  (hy : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s j) (@List.cons.{0} NLogN.Item (NLogN.Item.int y) lj)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.compareEq S i j tmp work dst) s
    (@NLogN.IState.upd S s dst
      (@ite.{1} (List.{0} NLogN.Item) (@Eq.{1} Int x y) (Int.instDecidableEq x y)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark (@NLogN.IState.G S s dst)) (@NLogN.IState.G S s dst)))
    (KoanaKPaths.Machine.compareCost x y) := by sorry
