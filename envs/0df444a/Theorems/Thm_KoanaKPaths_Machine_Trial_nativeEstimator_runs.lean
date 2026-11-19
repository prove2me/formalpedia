-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_nativeEstimator_runs
-- name    : KoanaKPaths.Machine.Trial.nativeEstimator_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:20:35.781091+00:00
-- url     : https://prove2.me/theorems/6db0beb5-5c31-4bee-8129-38d88825c96c
-- title:
--   Native computation of the median-of-means estimator fraction
-- statement:
--   Let $A$ be a directed graph, $k\ge1$, and $a,b$ natural accuracy and confidence controls. Assume the estimator-ready native state and a coin prefix encoding a complete sample $\omega$. Put $M=1024k^3 4^a$, $q=2b+1$, and let $Z_{ij}$ be the trial numerators decoded from its $qM$ blocks. The estimator program reaches a state whose numerator and denominator output registers are the singleton integers
--   $$\operatorname{median}_{i<q}\sum_{j<M}Z_{ij},\qquad Mk^k k!.$$
--   It preserves input position and external output and runs within $\operatorname{estimatorCost}(n,k,a,b,|A|)$. This is exact fraction computation for the walk coefficient tensor; the theorem itself asserts no probability estimate.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeEstimator.lean, line 17; source snapshot SHA-256 5286a1db7a25a97e5822f775ecfa4d222721fc2f93ab00af3e8e1e991ca9bed0.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
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

theorem KoanaKPaths.Machine.Trial.nativeEstimator_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k a b : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (ω : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
  (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.EstimatorReady n s k a b arcs)
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.ofFn.{0} Int (KoanaKPaths.Main.sampleBits n k a b)
            fun (j : Fin (KoanaKPaths.Main.sampleBits n k a b)) => KoanaKPaths.Main.sgn (ω j)))
        tail)),
  @Exists.{1} (NLogN.IState KoanaKPaths.Machine.Wedge.NS) fun (s' : NLogN.IState KoanaKPaths.Machine.Wedge.NS) =>
    And
      (@NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
        KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.nativeEstimator s s'
        (KoanaKPaths.Machine.Trial.estimatorCost n k a b (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)))
      (And
        (@Eq.{1} (List.{0} NLogN.Item)
          (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s'
            (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Wedge.NS) (nat_lit 126)
              (@Fin.instOfNat KoanaKPaths.Machine.Wedge.NS
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 126))))
          (@List.cons.{0} NLogN.Item
            (NLogN.Item.int
              (@Nat.cast.{0} Int instNatCastInt
                (HypergraphUnreliability.FPRAS.Frac.num
                  (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                      (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                      (fun (x : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool) =>
                        Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                        (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                        (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                      (KoanaKPaths.Main.samplesEquiv n k a b) ω)))))
            (@List.nil.{0} NLogN.Item)))
        (And
          (@Eq.{1} (List.{0} NLogN.Item)
            (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s'
              (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Wedge.NS) (nat_lit 127)
                (@Fin.instOfNat KoanaKPaths.Machine.Wedge.NS
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127))))
                  (nat_lit 127))))
            (@List.cons.{0} NLogN.Item
              (NLogN.Item.int
                (@Nat.cast.{0} Int instNatCastInt
                  (HypergraphUnreliability.FPRAS.Frac.den
                    (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                        (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (fun (x : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool) =>
                          Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                            (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                              Fin (KoanaKPaths.Main.groupTrials k a) →
                                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                          (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                          (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                            (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                              Fin (KoanaKPaths.Main.groupTrials k a) →
                                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                        (KoanaKPaths.Main.samplesEquiv n k a b) ω)))))
              (@List.nil.{0} NLogN.Item)))
          (And
            (@Eq.{1} Nat (@NLogN.IState.ip KoanaKPaths.Machine.Wedge.NS s')
              (@NLogN.IState.ip KoanaKPaths.Machine.Trial.NS s))
            (@Eq.{1} (List.{0} Bool) (@NLogN.IState.out KoanaKPaths.Machine.Wedge.NS s')
              (@NLogN.IState.out KoanaKPaths.Machine.Trial.NS s))))) := by sorry
