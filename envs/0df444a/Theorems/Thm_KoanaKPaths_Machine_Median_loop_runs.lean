-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Median_loop_runs
-- name    : KoanaKPaths.Machine.Median.loop_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:21:55.911334+00:00
-- url     : https://prove2.me/theorems/df02ac7a-e1e0-4a4f-b473-07309d75e24b
-- title:
--   Execute a bounded binary search for a sample order statistic
-- statement:
--   Let $x_1,\ldots,x_m$ be framed integer sample records of width at most $w$, with $w\ge1$. Let natural-number endpoints $\mathrm{lo},\mathrm{hi}$ have width at most $w$, let the threshold be the unary value $t$, and let the loop fuel be $L$ markers. With the midpoint, count and comparison scratch stacks empty and the halving ruler set to two, the median-search loop consumes its fuel and returns
--   $$
--   (\mathrm{lo}',\mathrm{hi}')=\operatorname{searchBounds}\bigl(q\mapsto t\le\#\{j:x_j\le q\},L,\mathrm{lo},\mathrm{hi}\bigr).
--   $$
--   All records, the threshold and saved data are preserved. Its charged running time is at most
--   $$
--   10000(w+L+1)(m+1)L+30.
--   $$
--   The theorem verifies the bounded native search itself; the order-statistic interpretation is supplied by the surrounding median argument.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/MedianLoop.lean, line 25; source snapshot SHA-256 7349caf4b8d792a0ffd7d0e26d93a2d72aebf04c903af29f564508236a0508db.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Median.loop_runs :
∀ (I : List.{0} NLogN.Sym) (L : Nat) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int)
  (t lo hi w : Nat) (rt lt ht rult : List.{0} NLogN.Item),
  @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Fuel)
      (@List.replicate.{0} NLogN.Item L NLogN.Item.mark) →
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark rt)) →
      @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt lo)) lt) →
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt hi)) ht) →
          @Eq.{1} (List.{0} NLogN.Item)
              (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)
              (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))
                rult) →
            @Eq.{1} (List.{0} NLogN.Item)
                (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
                (@List.nil.{0} NLogN.Item) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
                  (@List.nil.{0} NLogN.Item) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
                    (@List.replicate.{0} NLogN.Item t NLogN.Item.mark) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
                      (@List.nil.{0} NLogN.Item) →
                    @Eq.{1} (List.{0} NLogN.Item)
                        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)
                        (@List.nil.{0} NLogN.Item) →
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w →
                        @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt lo)) w →
                          @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt hi)) w →
                            (∀ (x : Int),
                                @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
                                  @LE.le.{0} Nat instLENat (NLogN.zsz x) w) →
                              @NLogN.IRuns KoanaKPaths.Machine.Median.NS
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
                                (@Fin.elim0.{1}
                                  (NLogN.IStmt KoanaKPaths.Machine.Median.NS
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                KoanaKPaths.Machine.Median.loop s
                                (KoanaKPaths.Machine.Median.boundsState s
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  (@KoanaKPaths.Machine.Median.searchBounds
                                    (fun (mid : Nat) =>
                                      @LE.le.{0} Nat instLENat t
                                        (KoanaKPaths.Machine.Median.countLE (@Nat.cast.{0} Int instNatCastInt mid) xs))
                                    (fun (a : Nat) =>
                                      Nat.decLe t
                                        (KoanaKPaths.Machine.Median.countLE (@Nat.cast.{0} Int instNatCastInt a) xs))
                                    L lo hi)
                                  lt ht)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w L)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} Int xs)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    L)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by sorry
