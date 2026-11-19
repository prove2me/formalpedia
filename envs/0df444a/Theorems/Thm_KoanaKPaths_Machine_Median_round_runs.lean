-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Median_round_runs
-- name    : KoanaKPaths.Machine.Median.round_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:33.114778+00:00
-- url     : https://prove2.me/theorems/05d4789e-4d4e-4bb9-a1d2-d0c5383a53bd
-- title:
--   One midpoint-counting round of native median search
-- statement:
--   Let a framed sample list $x_1,\ldots,x_m$ and natural endpoints $\mathrm{lo},\mathrm{hi}$ have integer widths at most $w\ge1$. Suppose the threshold is a unary count $t$, the halving ruler is two, and all midpoint, scan and comparison scratch stacks are empty. Set
--   $$
--   q=\left\lfloor\frac{\mathrm{lo}+\mathrm{hi}}2\right\rfloor,\qquad h=\#\{j:x_j\le q\}.
--   $$
--   The native round changes only the endpoint registers, returning $(\mathrm{lo},q)$ if $t\le h$ and $(q+1,\mathrm{hi})$ otherwise. It restores the sample records, threshold and scratch stacks. The running time is at most
--   $$
--   8000(w+1)(m+1).
--   $$
--   This is the operational refinement of one binary-search step for the required sample order statistic.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/MedianRound.lean, line 34; source snapshot SHA-256 0948f2eeddd372990fcd50fce4e11ec5fac784f4f5793a290b43cb76ac62134d.

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

theorem KoanaKPaths.Machine.Median.round_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int) (t lo hi w : Nat)
  (rt lt ht rult : List.{0} NLogN.Item)
  (hrec :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark rt)))
  (hl :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt lo)) lt))
  (hh :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt hi)) ht))
  (hrul :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))) rult))
  (hmid :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
      (@List.nil.{0} NLogN.Item))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.nil.{0} NLogN.Item))
  (hthr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
      (@List.nil.{0} NLogN.Item))
  (hf :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)
      (@List.nil.{0} NLogN.Item))
  (hlo : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt lo)) w)
  (hhi : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt hi)) w)
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.round s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@Prod.fst.{0, 0} Nat Nat (KoanaKPaths.Machine.Median.nextBounds xs t lo hi))))
          lt))
      KoanaKPaths.Machine.Median.Hi
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Prod.snd.{0, 0} Nat Nat (KoanaKPaths.Machine.Median.nextBounds xs t lo hi))))
        ht))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 8000) (instOfNatNat (nat_lit 8000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by sorry
