-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_program_exec
-- name    : KoanaKPaths.Machine.ArrayLookup.program_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:28.033872+00:00
-- url     : https://prove2.me/theorems/804bc99d-f75d-43a6-afde-da2bb0f28eb5
-- title:
--   Readonly lookup in the coordinate-array database
-- statement:
--   Suppose a native lookup database begins with marked array frames $A_1,\ldots,A_m$, followed by a marked target array $X$. Its unary forward counter has $m$ markers followed by a non-marker tail, and the backward and temporary counters are empty. The lookup program changes only its output stack:
--   $$\operatorname{Out}_{\rm after}=\operatorname{reverse}(X)\mathbin{+\!+}\operatorname{Out}_{\rm before},\qquad t=\operatorname{lookupCost}((A_1,\ldots,A_m),X).$$
--   The output consists of integer entries without an added delimiter. The cost is the sum of the forward skip, target copy, and backward restoration charges. In particular the original database, cache, counters, input position, and external output are restored. The result supplies a reusable nondestructive lookup contract.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayLookup.lean, line 200; source snapshot SHA-256 ac617e67ff08d0f33b49fb86fd15b78d1344a41d27da0a01d9424f89a5034729.

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

theorem KoanaKPaths.Machine.ArrayLookup.program_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArrayLookup.NS) (pre : List.{0} (List.{0} Int))
  (target : List.{0} Int) (rest ct : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) pre) NLogN.Item.mark) ct))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.ArrayLookup.frames pre) (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int target))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark rest)))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.ArrayLookup.program s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Out
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int target))
        (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Out)))
    (KoanaKPaths.Machine.ArrayLookup.lookupCost pre target) := by sorry
