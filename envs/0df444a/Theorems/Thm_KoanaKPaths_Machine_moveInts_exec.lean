-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
-- name    : KoanaKPaths.Machine.moveInts_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:51.304278+00:00
-- url     : https://prove2.me/theorems/72573847-b0e7-471a-b8a8-e65a2e80ab8f
-- title:
--   Move a delimited integer array with exact reversal cost
-- statement:
--   Let source and destination be distinct native registers. Suppose the source begins with an integer list $X$, followed by a tail whose first item is not an integer. The move-integers loop consumes precisely this prefix and produces
--   $$
--   \operatorname{src}'=\mathrm{tail},\qquad\operatorname{dst}'=\operatorname{reverse}X\mathbin{+\!+}\operatorname{dst}.
--   $$
--   All other registers and the input/output state are unchanged. Its exact charged time is
--   $$
--   C_{\rm move}(X)=30+\sum_{x\in X}\bigl(2\mu(\beta x)+49\bigr),
--   $$
--   where $\beta(x)$ is native integer width and $\mu$ is the primitive move charge. The stopping tail may be a marker, another noninteger item or the empty stack. This is the basic framed-array transport rule underlying coefficient and cached-sign database operations.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayNative.lean, line 24; source snapshot SHA-256 8e30aa9c861f6c9017c39a3ff6d5dbe2efed016c849535a9a36b0a610cfc1f0f.

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

theorem KoanaKPaths.Machine.moveInts_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst) (s : NLogN.IState S)
  (xs : List.{0} Int) (tail : List.{0} NLogN.Item)
  (ht :
    Not
      (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.zero)
        (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.pos)
          (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.neg))))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.moveInts S src dst) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs)) (@NLogN.IState.G S s dst)))
    (KoanaKPaths.Machine.moveIntsCost xs) := by sorry
