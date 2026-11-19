-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Balanced_insert_exec
-- name    : KoanaKPaths.Machine.Balanced.insert_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:56.825846+00:00
-- url     : https://prove2.me/theorems/877567d6-09c8-4cc1-aca9-e6d35dccd4ac
-- title:
--   Execute the carry phase of a balanced-sum insertion
-- statement:
--   Suppose a balanced-sum occupancy stack begins with $r$ occupied digits, followed by either an unoccupied digit or its delimiter, and the corresponding partial sums are $y_1,\ldots,y_r$. Let the carry stack contain $x$ and let the restoration stack be empty. The insertion program combines the occupied prefix into
--   $$
--   x'=x+\sum_{j=1}^{r}y_j,
--   $$
--   replaces its $r$ occupied digits by zero digits, and installs one occupied digit and the new partial sum $x'$. The carry and restoration stacks return to their tails. If $z$ records whether the stopping item was a zero digit, its exact cost is
--   $$
--   C_{\rm merge}(x,\mathbf y)+(27\text{ if }z\text{ else }26)+3+33r+30+2\mu(\beta(x'))+19,
--   $$
--   where $\beta$ is integer width and $\mu$ is the primitive integer-move charge. This is the carry operation underlying balanced summation.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/BalancedNative.lean, line 103; source snapshot SHA-256 f34dc4bd9ef48b1a92003176676bd5aad1f473ea3f28f6118d43936d58ec94f5.

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

theorem KoanaKPaths.Machine.Balanced.insert_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Balanced.NS) (x : Int) (ys : List.{0} Int)
  (zero : Bool) (bt pt ct : List.{0} NLogN.Item)
  (hb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
          (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (KoanaKPaths.Machine.Balanced.stopBits zero bt)))
  (hp :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Partials)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) pt))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Carry)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int x) ct))
  (hr :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Balanced.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Balanced.insert s
    (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Balanced.NS s KoanaKPaths.Machine.Balanced.Bits
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.replicate.{0} NLogN.Item (@List.length.{0} Int ys)
              (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (KoanaKPaths.Machine.Balanced.nextBits zero bt))))
        KoanaKPaths.Machine.Balanced.Partials
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x
              (@List.sum.{0} Int Int.instAdd
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) ys)))
          pt))
      KoanaKPaths.Machine.Balanced.Carry ct)
    (KoanaKPaths.Machine.Balanced.insertCost x ys zero) := by sorry
