-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_BitCounter_toMarks_runs
-- name    : KoanaKPaths.Machine.BitCounter.toMarks_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:19:35.649691+00:00
-- url     : https://prove2.me/theorems/feb1447e-bf3e-404b-8d03-b31b113dbc4a
-- title:
--   Convert a nonnegative binary integer to unary in linear value time
-- statement:
--   Let a source stack contain the nonnegative integer $n$ above an arbitrary saved tail. Assume the destination count stack has a nonmarker at its top and the conversion temporary stack is empty. The binary-to-unary program consumes the integer and creates exactly $n$ count markers:
--   $$
--   \operatorname{Count}_{\rm final}=\operatorname{mark}^{,n}\mathbin{+\!+}\operatorname{Count}_{\rm initial}.
--   $$
--   All scratch storage, saved tails and other state components are restored. The charged running time is bounded by
--   $$
--   1000(n+1).
--   $$
--   The bound is linear in the represented value rather than its binary length, as required for a subsequent loop with $n$ iterations. This theorem connects binary address calculations to the unary counters used by native array and sign lookup.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeBitCounter.lean, line 187; source snapshot SHA-256 33560a6a9a6de993a978544cc32a39e6071e781a299520a1a3f46cd0e93016e4.

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
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.BitCounter.toMarks_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.BitCounter.NS) (n : Nat) (st : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) st))
  (ht :
    @Ne.{1} NLogN.Cls
      (NLogN.cls
        (@List.head?.{0} NLogN.Item
          (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)))
      NLogN.Cls.mark)
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.BitCounter.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.BitCounter.toMarks s
    (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Source st)
      KoanaKPaths.Machine.BitCounter.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item n NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.BitCounter.NS s KoanaKPaths.Machine.BitCounter.Count)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by sorry
