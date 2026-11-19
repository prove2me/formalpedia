-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
-- name    : KoanaKPaths.Machine.copyMoveMarks_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:38.720481+00:00
-- url     : https://prove2.me/theorems/35f89697-5dc2-4726-a808-8612007f3fb1
-- title:
--   Consume a unary marker prefix and make two copies
-- statement:
--   Let source, destination and temporary registers be pairwise distinct. Suppose the source stack begins with $m$ markers followed by a nonmarker tail. The marker-copying program consumes this prefix and prepends $m$ markers to each of the other two stacks:
--   $$
--   \operatorname{src}'=\mathrm{tail},\quad\operatorname{dst}'=\operatorname{mark}^{,m}\mathbin{+\!+}\operatorname{dst},\quad\operatorname{tmp}'=\operatorname{mark}^{,m}\mathbin{+\!+}\operatorname{tmp}.
--   $$
--   It preserves every original destination and temporary tail, the input/output state and all other registers. Its exact running cost is
--   $$
--   33m+30.
--   $$
--   The marker prefix can encode an arbitrary unary count, including zero. This operation is the elementary consumption-and-duplication stage used to construct reusable unary loop templates in the native graph and sampling programs.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeMarks.lean, line 143; source snapshot SHA-256 f11453357c827c9f073c70c6f785ed2027d21b6c69f3c4a5894d8ecea7743cbb.

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

theorem KoanaKPaths.Machine.copyMoveMarks_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst tmp : Fin S) (hsd : @Ne.{1} (Fin S) src dst)
  (hst : @Ne.{1} (Fin S) src tmp) (hdt : @Ne.{1} (Fin S) dst tmp) (s : NLogN.IState S) (m : Nat)
  (tail : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.copyMoveMarks S src dst tmp) s
    (@NLogN.IState.upd S
      (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) (@NLogN.IState.G S s dst)))
      tmp
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) (@NLogN.IState.G S s tmp)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) m)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
