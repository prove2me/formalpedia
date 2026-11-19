-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_labelLoop_runs
-- name    : KoanaKPaths.Machine.Trial.labelLoop_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:16.808651+00:00
-- url     : https://prove2.me/theorems/2be4f3fa-c764-4f88-9d41-db7a6d721c44
-- title:
--   Loading a contiguous vertex-label block from the sign cache
-- statement:
--   Let $X$ be a cached list of signs and let the vertex header be $v$. For $r+m\le k$, assume the label counter contains $m$ markers, the row register is $r$, every address $vk+j$ for $j<k$ is valid, and its arithmetic computation and counters fit width $w\ge1$. The label loop prepends
--   $$\operatorname{reverse}(X_{vk+r},\ldots,X_{vk+r+m-1})$$
--   to the wedge vector, sets the row to $r+m$, and empties the counter. It preserves the cache, headers, lookup helpers, and other state. Its bound is $m\,\operatorname{labelIterationCost}(X,w)+30$, where each iteration includes one bounded address evaluation, readonly sign lookup, and increment. This implements loading shared vertex labels.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/LabelLoop.lean, line 20; source snapshot SHA-256 7adfbac758c50cd10570d4ba053f9e537ed3ff36668efc647c284e2ae999fdec.

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

theorem KoanaKPaths.Machine.Trial.labelLoop_runs :
∀ (I : List.{0} NLogN.Sym) (m : Nat) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int) (k v r w : Nat)
  (kt vt rt tt rest : List.{0} NLogN.Item),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w →
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r m) k →
      @Eq.{1} (List.{0} NLogN.Item)
          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
          (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) →
        @Eq.{1} (List.{0} NLogN.Item)
            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
              (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
                (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127))))
                  (nat_lit 54))))
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt) →
          @Eq.{1} (List.{0} NLogN.Item)
              (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
              (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt v)) vt) →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Row)
                (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt r)) rt) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
                  (@List.cons.{0} NLogN.Item
                    (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
                    (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                      (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                      (KoanaKPaths.Machine.Trial.signItems xs) rest) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
                      (@List.nil.{0} NLogN.Item) →
                    @Eq.{1} (List.{0} NLogN.Item)
                        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
                        (@List.nil.{0} NLogN.Item) →
                      @Eq.{1} (List.{0} NLogN.Item)
                          (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
                          (@List.nil.{0} NLogN.Item) →
                        @Eq.{1} (List.{0} NLogN.Item)
                            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
                            (@List.nil.{0} NLogN.Item) →
                          @Eq.{1} (List.{0} NLogN.Item)
                              (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
                              (@List.nil.{0} NLogN.Item) →
                            (∀ (x : Int),
                                @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
                                  Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                    (@Eq.{1} Int x
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
                              (∀ (row : Nat),
                                  @LT.lt.{0} Nat instLTNat row k →
                                    @LE.le.{0} Nat instLENat
                                      (@KoanaKPaths.Machine.Arithmetic.Expr.width
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (KoanaKPaths.Machine.Trial.labelValues k v row)
                                        KoanaKPaths.Machine.Trial.labelExpr)
                                      w) →
                                @LE.le.{0} Nat instLENat
                                    (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w →
                                  (∀ (row : Nat),
                                      @LE.le.{0} Nat instLENat row k →
                                        @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt row)) w) →
                                    (∀ (row : Nat),
                                        @LT.lt.{0} Nat instLTNat row k →
                                          @LT.lt.{0} Nat instLTNat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) v k) row)
                                            (@List.length.{0} Int xs)) →
                                      @NLogN.IRuns KoanaKPaths.Machine.Trial.NS
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
                                        (@Fin.elim0.{1}
                                          (NLogN.IStmt KoanaKPaths.Machine.Trial.NS
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        KoanaKPaths.Machine.Trial.labelLoop s
                                        (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
                                          (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
                                            (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s
                                              KoanaKPaths.Machine.Trial.LabelCounter (@List.nil.{0} NLogN.Item))
                                            KoanaKPaths.Machine.Trial.Row
                                            (@List.cons.{0} NLogN.Item
                                              (NLogN.Item.int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    m)))
                                              rt))
                                          KoanaKPaths.Machine.Wedge.V
                                          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                                            (List.{0} NLogN.Item)
                                            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item)
                                              (@List.instAppend.{0} NLogN.Item))
                                            (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
                                              (@List.reverse.{0} Int (KoanaKPaths.Machine.Trial.labelBlock xs k v r m)))
                                            (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
                                              KoanaKPaths.Machine.Wedge.V)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (KoanaKPaths.Machine.Trial.labelIterationCost xs w) m)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
