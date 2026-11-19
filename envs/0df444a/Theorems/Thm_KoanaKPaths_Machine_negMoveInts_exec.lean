-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_negMoveInts_exec
-- name    : KoanaKPaths.Machine.negMoveInts_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:25.046433+00:00
-- url     : https://prove2.me/theorems/bcb5e329-cbfa-4598-8d27-6bfd678d9e50
-- title:
--   Negate and move a delimited integer array with exact cost
-- statement:
--   Let source and destination be distinct registers and suppose the source holds an integer prefix $X$ followed by a noninteger tail. The negate-and-move loop consumes that prefix and prepends
--   $$
--   \operatorname{reverse}[-x:x\in X]
--   $$
--   to the destination. The source tail, destination tail, all unrelated stacks and the input/output state are preserved. Its exact running cost is
--   $$
--   C_{\rm move}(X)+20|X|,
--   $$
--   where $C_{\rm move}(X)=30+\sum_{x\in X}(2\mu(\beta x)+49)$ is the exact ordinary array-transfer charge. The extra $20$ is the native negation charge for each integer. This operation implements signed coefficient-block transfers without assuming positive coefficients or bounded numerical values.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayNative.lean, line 287; source snapshot SHA-256 8e30aa9c861f6c9017c39a3ff6d5dbe2efed016c849535a9a36b0a610cfc1f0f.

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

theorem KoanaKPaths.Machine.negMoveInts_exec :
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
    (@KoanaKPaths.Machine.negMoveInts S src dst) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item (fun (z : Int) => NLogN.Item.int (@Neg.neg.{0} Int Int.instNegInt z))
          (@List.reverse.{0} Int xs))
        (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (KoanaKPaths.Machine.moveIntsCost xs)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) (@List.length.{0} Int xs))) := by sorry
