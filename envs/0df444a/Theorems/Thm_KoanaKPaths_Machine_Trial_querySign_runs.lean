-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_querySign_runs
-- name    : KoanaKPaths.Machine.Trial.querySign_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:30.245127+00:00
-- url     : https://prove2.me/theorems/fdd467d1-f0c5-4877-a0b8-b159f67dbe78
-- title:
--   Read a physical cached-sign index and restore the cache
-- statement:
--   Let the logical sign list be $x_0,\ldots,x_{T-1}$, stored in the sign database in physical reverse order. Suppose the source register contains a valid physical index $i<T$ and the binary conversion and sign lookup scratch stacks are empty. The query-sign program consumes the source integer and prepends
--   $$
--   (\operatorname{reverse}x)_i=x_{T-1-i}
--   $$
--   to the sign-output register, preserving the database and every other state component. Its charged running time is at most
--   $$
--   1100(i+1)+C_{\rm lookup}\bigl(\operatorname{take}_i\mathcal A;[(\operatorname{reverse}x)_i]\bigr),
--   $$
--   where $\mathcal A$ is the list of singleton records of the reversed sign list and $C_{\rm lookup}$ is the declared restorable record-lookup charge. The separate address translator converts logical sign addresses to these physical indices.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/SignQuery.lean, line 24; source snapshot SHA-256 c63e32c92f36c5d0c2587f3149e83323ba963a1eda98bc8d79ad04e8031bcbfe.

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

theorem KoanaKPaths.Machine.Trial.querySign_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int)
  (i : Fin (@List.length.{0} Int xs)) (st rest : List.{0} NLogN.Item)
  (hsource :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val (@List.length.{0} Int xs) i))) st))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hindex :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hback :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.querySign s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source st)
      KoanaKPaths.Machine.SignLookup.Out
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) (@List.reverse.{0} Int xs) (@Fin.val (@List.length.{0} Int xs) i)
            (@of_eq_true
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                (@List.length.{0} Int (@List.reverse.{0} Int xs)))
              (@Eq.trans.{1} Prop
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                  (@List.length.{0} Int (@List.reverse.{0} Int xs)))
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i) (@List.length.{0} Int xs)) True
                (@congrArg.{1, 1} Nat Prop (@List.length.{0} Int (@List.reverse.{0} Int xs)) (@List.length.{0} Int xs)
                  (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)) (@List.length_reverse.{0} Int xs))
                (@Fin.is_lt._simp_1 (@List.length.{0} Int xs) i)))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1100) (instOfNatNat (nat_lit 1100)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val (@List.length.{0} Int xs) i)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (KoanaKPaths.Machine.SignLookup.lookupCost
        (@List.take.{0} (List.{0} Int) (@Fin.val (@List.length.{0} Int xs) i)
          (@List.map.{0, 0} Int (List.{0} Int) (fun (x : Int) => @List.cons.{0} Int x (@List.nil.{0} Int))
            (@List.reverse.{0} Int xs)))
        (@List.cons.{0} Int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) (@List.reverse.{0} Int xs) (@Fin.val (@List.length.{0} Int xs) i)
            (@of_eq_true
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                (@List.length.{0} Int (@List.reverse.{0} Int xs)))
              (@Eq.trans.{1} Prop
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)
                  (@List.length.{0} Int (@List.reverse.{0} Int xs)))
                (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i) (@List.length.{0} Int xs)) True
                (@congrArg.{1, 1} Nat Prop (@List.length.{0} Int (@List.reverse.{0} Int xs)) (@List.length.{0} Int xs)
                  (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} Int xs) i)) (@List.length_reverse.{0} Int xs))
                (@Fin.is_lt._simp_1 (@List.length.{0} Int xs) i))))
          (@List.nil.{0} Int)))) := by sorry
