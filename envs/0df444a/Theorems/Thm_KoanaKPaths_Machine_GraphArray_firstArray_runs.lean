-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_GraphArray_firstArray_runs
-- name    : KoanaKPaths.Machine.GraphArray.firstArray_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:21:52.83388+00:00
-- url     : https://prove2.me/theorems/a74c40d3-d214-40af-9043-d05078d72421
-- title:
--   Constructing one signed first-layer exterior array
-- statement:
--   Let $v$ be a list of $d$ signs and $z\in\{1,-1\}$. Assume the wedge depth is encoded by $d$ unary markers, the label and sign registers contain $v$ and $z$, and the three wedge helper stacks are empty. The first-array program consumes $z$ and prepends the marked coordinate array
--   $$z\,\operatorname{wedgeReverse}(v,U_d),\qquad t\le10^6(d+2)^2 2^d,$$
--   where $U_d=(1,0,\ldots,0)$ has $2^d$ entries and represents the exterior-algebra unit. The label vector, depth, all original tails, input position, and output are preserved. This realizes an individual signed vertex contribution in the initial graph-sketch layer.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/FirstArray.lean, line 38; source snapshot SHA-256 901374d08b116891ff14b7759e96412152cbf7335705b4b8a9bb20829240ae14.

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

theorem KoanaKPaths.Machine.GraphArray.firstArray_runs :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.GraphArray.NS) (vs : List.{0} Int) (z : Int)
  (td tv st : List.{0} NLogN.Item) (hdt : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.D)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int vs) NLogN.Item.mark) td))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.V)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv))
  (hsgn :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) st))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hdc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (ha :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.GraphArray.firstArray s
    (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign st)
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} Int Int
            (fun (x : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) z x)
            (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs
              (KoanaKPaths.Machine.GraphArray.unitArray (@List.length.{0} Int vs)))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Current))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000000) (instOfNatNat (nat_lit 1000000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int vs)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs))) := by sorry
