-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_GraphArray_weightedAdd_runs
-- name    : KoanaKPaths.Machine.GraphArray.weightedAdd_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:03.128086+00:00
-- url     : https://prove2.me/theorems/2b00a96e-7a2e-4307-872a-6c55f26c24d2
-- title:
--   Bit-cost contract for adding a signed coordinate array
-- statement:
--   Let $X$ and $Y$ be integer arrays of equal length $r$, with all entries of bit width at most $w$, stored in marked source and accumulator frames. Let the sign register contain $z\in\{1,-1\}$. The weighted-add program consumes the source frame and sign and replaces the accumulator frame by
--   $$Z_j=zX_j+Y_j\quad(0\le j<r),\qquad t\le10000(w+2)(r+1).$$
--   The existing stack tails, input position, output, and all other registers are preserved. Bit width is the bit length of absolute value. This routine performs the shared-sign linear combinations in the recursive sketch without a unit-cost assumption for long integers.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WeightedAccumulate.lean, line 15; source snapshot SHA-256 2c02457740c8d824232f54db96b6800608dca805c95151518fff2807c947b63b.

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

theorem KoanaKPaths.Machine.GraphArray.weightedAdd_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.GraphArray.NS) (z : Int) (xs ys : List.{0} Int)
  (st atail sigtail : List.{0} NLogN.Item)
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int ys))
  (hsign :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) sigtail))
  (hsrc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.A)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark st)))
  (hacc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) (@List.cons.{0} NLogN.Item NLogN.Item.mark atail)))
  (w : Nat)
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (hy :
    ∀ (y : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) ys y →
        @LE.le.{0} Nat instLENat (NLogN.zsz y) w),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.GraphArray.weightedAdd s
    (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.A st)
        KoanaKPaths.Machine.GraphArray.Sign sigtail)
      KoanaKPaths.Machine.Accumulate.Acc
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.zipWith.{0, 0, 0} Int Int Int
            (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2)
            (@List.map.{0, 0} Int Int
              (fun (x : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) z x) xs)
            ys))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark atail)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by sorry
