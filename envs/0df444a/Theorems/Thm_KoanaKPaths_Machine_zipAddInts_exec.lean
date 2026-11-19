-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_zipAddInts_exec
-- name    : KoanaKPaths.Machine.zipAddInts_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:21:33.603208+00:00
-- url     : https://prove2.me/theorems/f07bb886-0828-4c4f-a469-32c17ca6e079
-- title:
--   Adding equally long integer arrays into a reversed output prefix
-- statement:
--   Let source, second-source, and output native registers be pairwise distinct. Suppose their input prefixes are integer lists $X,Y$ of the same length, and the first source tail begins with a non-integer. The zip-add loop consumes both input prefixes and prepends the reversed coordinatewise sum:
--   $$\operatorname{Out}_{\rm after}=\operatorname{reverse}(X+Y)\mathbin{+\!+}\operatorname{Out}_{\rm before}.$$
--   It restores the two original tails and preserves other registers, input position, and output. Its exact time is $30+\sum_j[\operatorname{addIntCost}(\operatorname{bits}(X_j)+\operatorname{bits}(Y_j))+30]$. No sign or positivity restriction is imposed. This provides the bit-charged integer addition stage for exterior-array recombination and graph accumulation.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ArrayNative.lean, line 165; source snapshot SHA-256 8e30aa9c861f6c9017c39a3ff6d5dbe2efed016c849535a9a36b0a610cfc1f0f.

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

theorem KoanaKPaths.Machine.zipAddInts_exec :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst out : Fin S) (hsd : @Ne.{1} (Fin S) src dst)
  (hso : @Ne.{1} (Fin S) src out) (hdo : @Ne.{1} (Fin S) dst out) (s : NLogN.IState S) (xs ys : List.{0} Int)
  (tail tail' : List.{0} NLogN.Item)
  (ht :
    Not
      (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.zero)
        (Or (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.pos)
          (@Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.neg))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int ys))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s dst)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) tail')),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.zipAddInts S src dst out) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst tail') out
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (@List.zipWith.{0, 0, 0} Int Int Int
              (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2) xs ys)))
        (@NLogN.IState.G S s out)))
    (KoanaKPaths.Machine.zipAddIntsCost xs ys) := by sorry
