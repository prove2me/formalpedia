-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_groupFold_runs
-- name    : KoanaKPaths.Machine.Trial.groupFold_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:29.641203+00:00
-- url     : https://prove2.me/theorems/d6fc30f7-9f7f-482b-b459-6f5f80b9f5e6
-- title:
--   Collect exact trial-group sums in native record order
-- statement:
--   Let $k\ge1$ and let $\mathcal G=(G_1,\ldots,G_q)$ be groups of trial bit strings, each containing exactly $m$ trials. Suppose a ready graph state has a unary group counter $q$, a unary trial template $m$, empty trial-control scratch stacks, and a coin stack containing the concatenated encoded groups followed by a saved tail. The group-fold program consumes those bits and the group counter and prepends
--   $$
--   \operatorname{reverse}\left[\sum_{\omega\in G_j}Z(\omega):1\le j\le q\right]
--   $$
--   to its output-record stack. Here $Z(\omega)$ is the exact graph-trial numerator defined by the decoded label and sketch signs. Ready-state data and the coin tail are preserved. Its cost is at most
--   $$
--   (C_{\rm group}(n,k,|\mathrm{arcs}|,m)+31)q+30.
--   $$
--   This verifies deterministic collection of the independent-group samples used later in median amplification.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/GroupFold.lean, line 25; source snapshot SHA-256 4622fe12c2333ad46d4b63fb55bd15aa8608c0aace17f870c34f738f6de0014c.

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

theorem KoanaKPaths.Machine.Trial.groupFold_runs :
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
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss)
        NLogN.Item.mark))
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
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.groupsStream n k oss) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupFold s
    (@KoanaKPaths.Machine.Trial.groupFoldState n k s arcs oss tail)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (KoanaKPaths.Machine.Trial.groupNativeCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs) m)
          (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        (@List.length.{0} (List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)) oss))
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
