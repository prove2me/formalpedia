-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_predecessorRow_runs
-- name    : KoanaKPaths.Machine.Trial.predecessorRow_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:10.115956+00:00
-- url     : https://prove2.me/theorems/ab437a1d-aa79-4852-a057-21709da8916a
-- title:
--   Accumulating all previous sketch states for one predecessor vertex
-- statement:
--   Fix trial signs, graph layer $p\le k$, transition index $i<k-1$, target state $a<k$, and vertices $u,v<n$. Let the native core store $D_p$, and suppose the found flag correctly states whether $(u,v)$ is an arc. Start with previous-state index zero, $k$ counter markers, and the predecessor-sum prefix before state zero. The row loop updates the accumulator to
--   $$\sum_{(x,b)<_{\rm lex}(u+1,0)}\mathbf1_{(x,v)\in A}\,r_i(a,b,v)D_p(x,b).$$
--   The previous-state index becomes $k$ and its counter empties; other state is preserved. The bound is $(C+56)k+30$, with $C=\operatorname{predecessorCellCost}(nk,T,k,W)$, $T=\operatorname{trialBits}(n,k)$ and $W=100(1+n+k)^2$. Here $r_i(a,b,v)$ is the cached $\pm1$ transition sign for state pair $(a,b)$ and target vertex $v$. This processes one predecessor row.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/PredecessorRow.lean, line 22; source snapshot SHA-256 e774cb784edf791e2d2ade3267db6debcf68b91b9f28a0dfb6bc4e8fd7367972.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Trial.predecessorRow_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (p : Nat)
  (hp : @LE.le.{0} Nat instLENat p k)
  (i :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (a : Fin k) (v u : Fin n) (vt atail it ut bt accTail ft : List.{0} NLogN.Item)
  (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs p)
  (hV :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n v))) vt))
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val k a))) atail))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)))
        it))
  (hU :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n u))) ut))
  (hB :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousState)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) bt))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
  (hF :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Found)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (Bool.toNat
              (@Decidable.decide
                (@Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) (Fin n)) (Finset.{0} (Prod.{0, 0} (Fin n) (Fin n)))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Fin n) (Fin n)))
                    (Prod.{0, 0} (Fin n) (Fin n)) (@Finset.instSetLike.{0} (Prod.{0, 0} (Fin n) (Fin n))))
                  (@List.toFinset.{0} (Prod.{0, 0} (Fin n) (Fin n))
                    (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                      @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                    arcs)
                  (@Prod.mk.{0, 0} (Fin n) (Fin n) u v))
                (@Finset.decidableMem.{0} (Prod.{0, 0} (Fin n) (Fin n))
                  (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                    @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                  (@Prod.mk.{0, 0} (Fin n) (Fin n) u v)
                  (@List.toFinset.{0} (Prod.{0, 0} (Fin n) (Fin n))
                    (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                      @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                    arcs))))))
        ft))
  (hAcc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.ExteriorCoordinates.coefficientList k
            (@KoanaKPaths.Main.predSum n k arcs
              (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              p i a v (@Fin.val n u) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail))),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.predecessorRow s
    (@KoanaKPaths.Machine.Trial.predecessorRowState n k s ω arcs p i a v u k bt accTail)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (KoanaKPaths.Machine.Trial.predecessorCellCost
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n k) (KoanaKPaths.Main.trialBits n k) k
            (KoanaKPaths.Machine.Trial.wordWidth n k))
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        k)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
