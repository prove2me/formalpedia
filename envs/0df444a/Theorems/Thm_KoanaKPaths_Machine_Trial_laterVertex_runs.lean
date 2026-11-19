-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_laterVertex_runs
-- name    : KoanaKPaths.Machine.Trial.laterVertex_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:33.737375+00:00
-- url     : https://prove2.me/theorems/772ab1b1-04f7-4ff1-908c-9c66e2a0f8e7
-- title:
--   Computing the next-layer sketch row for one graph vertex
-- statement:
--   For a fixed trial, let $D_{i+1}$ be the current dense graph-sketch matrix, $i<k-1$, and $v<n$. Assume its canonical core state, the vertex and layer headers $v,i$, and empty state and predecessor counters. The later-vertex program increments the vertex to $v+1$ and prepends the $k$ marked arrays
--   $$D_{i+2}(v,a),\qquad 0\le a<k,$$
--   in reverse state order to the current bank. Other native registers, including the old matrix and sign cache, are restored. It runs within $\operatorname{laterVertexCost}(n,k,|A|)$, which includes loading $k$ labels, computing $k$ later cells, clearing temporary labels, and incrementing the vertex. This contract forms a row in one layer transition.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/LaterVertex.lean, line 23; source snapshot SHA-256 7b4c0edb63e72f2c79954278cf638d667f54d9529b169526e63d5bf85234fee4.

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

theorem KoanaKPaths.Machine.Trial.laterVertex_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (layer :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (v : Fin n) (vt it : List.{0} NLogN.Item)
  (hCore :
    @KoanaKPaths.Machine.Trial.Core n k s ω arcs
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Fin.val
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          layer)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n v))) vt))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              layer)))
        it))
  (hCounter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.nil.{0} NLogN.Item))
  (hPC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PredecessorCounter)
      (@List.nil.{0} NLogN.Item))
  (hBC :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.laterVertex s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n v)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          vt))
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames
          (@List.reverse.{0} (List.{0} Int)
            (@List.ofFn.{0} (List.{0} Int) k fun (a : Fin k) =>
              @KoanaKPaths.Main.denseLayer n k k arcs
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
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@Fin.val
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    layer)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                v a)))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.GraphArray.Current)))
    (KoanaKPaths.Machine.Trial.laterVertexCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)) := by sorry
