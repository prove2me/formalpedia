-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_loadVector_runs
-- name    : KoanaKPaths.Machine.Trial.loadVector_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:59.34758+00:00
-- url     : https://prove2.me/theorems/629287e5-87e9-484e-988e-c5147342a62d
-- title:
--   Load a vertex label vector from the shared sign cache
-- statement:
--   Let $x_0,\ldots,x_{T-1}$ be signs, and let the native headers contain $k,v,T$. Suppose every address $vk+r$, $r<k$, is valid, the address expressions and relevant header and row values have width at most $w\ge1$, the unary dimension template contains $k$ markers, and all label-loop and sign-lookup scratch stacks are empty. Loading the vector prepends
--   $$
--   [x_{vk+k-1},\ldots,x_{vk}]\mathbin{+\!+}[\operatorname{mark}]
--   $$
--   to its saved vector stack, preserving all other data. Its cost is at most
--   $$
--   C_{\rm label}(x,w)k+65k+2\beta(k)+95,
--   $$
--   where $C_{\rm label}(x,w)=500000(w+1)^2+10000(T+1)$ and $\beta$ is integer width. The reverse order is the coordinate convention expected by native exterior multiplication.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/LabelVector.lean, line 14; source snapshot SHA-256 928e5f8a812d49c32beac3237e00820f99e9f12351e9dba8fb22c5de5debec5c.

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
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.loadVector_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int) (k v w : Nat)
  (kt vt tt rest : List.{0} NLogN.Item)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hk :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 54))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt v)) vt))
  (hT :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest))
  (hD :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.D)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
  (hC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.nil.{0} NLogN.Item))
  (hL :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelTmp)
      (@List.nil.{0} NLogN.Item))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hi :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hxs :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (he :
    ∀ (row : Nat),
      @LT.lt.{0} Nat instLTNat row k →
        @LE.le.{0} Nat instLENat
          (@KoanaKPaths.Machine.Arithmetic.Expr.width (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (KoanaKPaths.Machine.Trial.labelValues k v row) KoanaKPaths.Machine.Trial.labelExpr)
          w)
  (hTw : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w)
  (hRw :
    ∀ (row : Nat),
      @LE.le.{0} Nat instLENat row k → @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt row)) w)
  (hvalid :
    ∀ (row : Nat),
      @LT.lt.{0} Nat instLTNat row k →
        @LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v k) row)
          (@List.length.{0} Int xs)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.loadVector s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (KoanaKPaths.Machine.Trial.labelBlock xs k v (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              k)))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (KoanaKPaths.Machine.Trial.labelIterationCost xs w) k)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65))) k))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt k))))
      (@OfNat.ofNat.{0} Nat (nat_lit 95) (instOfNatNat (nat_lit 95)))) := by sorry
