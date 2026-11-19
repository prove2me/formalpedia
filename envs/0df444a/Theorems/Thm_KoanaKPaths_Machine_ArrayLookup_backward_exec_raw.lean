-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_backward_exec_raw
-- name    : KoanaKPaths.Machine.ArrayLookup.backward_exec_raw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:59.640125+00:00
-- url     : https://prove2.me/theorems/b7a5a67c-e530-47d3-a85b-a284adf61770
-- title:
--   Restoring a skipped prefix of the array database
-- statement:
--   Let $A=(A_1,\ldots,A_m)$ be integer arrays stored as marked frames in the lookup cache. Suppose the backward counter has exactly $m$ leading markers followed by a non-marker tail. The backward restoration loop empties this prefix of the cache, consumes those counter markers, and prepends $m$ markers to the forward count. It restores the database prefix in the order
--   $$\operatorname{frames}(\operatorname{reverse}(\operatorname{map}(\operatorname{reverse},A))).$$
--   The exact charged time is the lookup library's $\operatorname{forwardCost}(A)$, the sum of each frame's integer-move charge and loop overhead. Existing stack tails, input position, output, and all other registers are preserved. This is the restoration half of readonly database lookup.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayLookup.lean, line 121; source snapshot SHA-256 ac617e67ff08d0f33b49fb86fd15b78d1344a41d27da0a01d9424f89a5034729.

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

theorem KoanaKPaths.Machine.ArrayLookup.backward_exec_raw :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArrayLookup.NS) (arrays : List.{0} (List.{0} Int))
  (rest ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Back)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark) ct))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Cache)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames arrays) rest)),
  @NLogN.IExec KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.ArrayLookup.backward s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Back ct)
          KoanaKPaths.Machine.ArrayLookup.Count
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark)
            (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Count)))
        KoanaKPaths.Machine.ArrayLookup.DB
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.ArrayLookup.reverseFrames arrays)
          (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.DB)))
      KoanaKPaths.Machine.ArrayLookup.Cache rest)
    (KoanaKPaths.Machine.ArrayLookup.forwardCost arrays) := by sorry
