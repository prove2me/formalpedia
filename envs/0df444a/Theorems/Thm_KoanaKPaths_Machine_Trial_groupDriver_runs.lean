-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_groupDriver_runs
-- name    : KoanaKPaths.Machine.Trial.groupDriver_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:33.4182+00:00
-- url     : https://prove2.me/theorems/32366ba6-10d0-4dbd-9e11-4b278bb7448d
-- title:
--   Computing an ordered list of group sums from trial tapes
-- statement:
--   Let $\Omega=(O_1,\ldots,O_q)$ be groups of trial bit blocks, each containing $m$ trials, with $k\ge1$. Assume the ready native graph state, unary templates for $q$ groups and $m$ trials, empty loop and copying helpers, and a coin stack containing these groups followed by a tail. The group driver consumes exactly this prefix and writes the marked record list
--   $$s_i=\sum_{\omega\in O_i}\operatorname{trialNumerator}(A,\omega),\qquad i=1,\ldots,q,$$
--   in the original group order. Other state is restored. The time is at most $(G+3000(W+m+1))(q+1)$, where $W=100(1+n+k)^2$ and $G=\operatorname{groupNativeCost}(n,k,|A|,m)$. This supplies the records on which confidence amplification takes a median.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GroupDriver.lean, line 22; source snapshot SHA-256 4c7cc92a7125f462367927ffee1cf01547c83a627cf80a40c10a3bf92b6462f1.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.groupDriver_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (oss : List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) (m : Nat) (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hlen :
    ∀ (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)),
      @Membership.mem.{0, 0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
          (List.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)))
          (@List.instMembership.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))) oss os →
        @Eq.{1} Nat (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os) m)
  (hQ :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupTemplate)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)
        NLogN.Item.mark))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCounter)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialTemplate)
      (@List.replicate.{0} NLogN.Item m NLogN.Item.mark))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hy :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.OuterCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.groupsStream n k oss) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupDriver s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Balanced.Records
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@KoanaKPaths.Machine.Trial.groupSums n k arcs oss))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Records))))
    (KoanaKPaths.Machine.Trial.groupDriverCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs) m
      (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)) := by sorry
