-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_duplicateTakeInts_exec
-- name    : KoanaKPaths.Machine.duplicateTakeInts_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:42.435251+00:00
-- url     : https://prove2.me/theorems/e6f3fc0b-f49d-4d41-93d0-c09976c98677
-- title:
--   Consume a counted integer array and create two reversed copies
-- statement:
--   Let the count, source and two destination registers be pairwise distinct. Suppose the unary count contains $m=|X|$ markers above a nonmarker tail and the source begins with the integer list $X$. The counted duplication program consumes that count and source prefix and prepends
--   $$
--   \operatorname{reverse}X
--   $$
--   to each destination, preserving all saved tails and other state. With $\beta$ the integer width, $D$ the duplication charge and $\mu$ the move charge, its exact cost is
--   $$
--   30+\sum_{x\in X}\bigl(D(\beta x)+17+2\mu(\beta x)+19+31\bigr).
--   $$
--   Only the count bounds the source prefix; its saved tail need not be an array delimiter. This contract duplicates a coefficient block while retaining exact integer-width accounting.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayNative.lean, line 228; source snapshot SHA-256 8e30aa9c861f6c9017c39a3ff6d5dbe2efed016c849535a9a36b0a610cfc1f0f.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
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

theorem KoanaKPaths.Machine.duplicateTakeInts_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (count src dst tmp : Fin S) (hcs : @Ne.{1} (Fin S) count src)
  (hcd : @Ne.{1} (Fin S) count dst) (hct : @Ne.{1} (Fin S) count tmp) (hsd : @Ne.{1} (Fin S) src dst)
  (hst : @Ne.{1} (Fin S) src tmp) (hdt : @Ne.{1} (Fin S) dst tmp) (s : NLogN.IState S) (xs : List.{0} Int)
  (tail ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int xs) NLogN.Item.mark) ct))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.duplicateTakeInts S count src dst tmp) s
    (@NLogN.IState.upd S
      (@NLogN.IState.upd S (@NLogN.IState.upd S (@NLogN.IState.upd S s count ct) src tail) dst
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs)) (@NLogN.IState.G S s dst)))
      tmp
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs)) (@NLogN.IState.G S s tmp)))
    (KoanaKPaths.Machine.duplicateTakeIntsCost xs) := by sorry
