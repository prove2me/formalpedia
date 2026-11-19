-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Wedge_call_exec
-- name    : KoanaKPaths.Machine.Wedge.call_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:03.854762+00:00
-- url     : https://prove2.me/theorems/a78f9874-da64-4d7f-aec9-330b430dbfdb
-- title:
--   Correctness and exact bit cost of the recursive right-wedge procedure
-- statement:
--   Let $v$ be a list of $d$ signs and $X$ an integer array of length $2^d$. Suppose marked native stacks hold $X$, the vector $v$ in decreasing coordinate order, and a depth prefix of $d$ markers followed by a non-marker tail; the three wedge helpers are empty. The single recursive wedge procedure consumes the input array, preserves vector and depth, and prepends the marked result
--   $$\operatorname{wedgeReverse}(v,X),\qquad t=\operatorname{wedgeCost}(v,X).$$
--   This is the right exterior product in subset-coordinate order. The exact recursive charge includes preparation, two half-array recursive calls, recombination, integer moves and arithmetic, and call overhead. All other stack tails, input position, and output are restored. This certifies the algorithm's core exterior operation.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WedgeExec.lean, line 24; source snapshot SHA-256 f9b3264b46968347905445250eb1e651a4a1e47acecdf9e4b28d071c439764b2.

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Wedge.call_exec :
∀ (I : List.{0} NLogN.Sym) (vs : List.{0} Int) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (xs : List.{0} Int)
  (ta td tv : List.{0} NLogN.Item),
  @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)) →
    (∀ (z : Int),
        @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
          Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Eq.{1} Int z
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) →
      @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark →
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
              (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
              (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark ta)) →
          @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.D)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                (@List.replicate.{0} NLogN.Item (@List.length.{0} Int vs) NLogN.Item.mark) td) →
            @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.V)
                (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                  (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                  (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.HC)
                  (@List.nil.{0} NLogN.Item) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.DC)
                    (@List.nil.{0} NLogN.Item) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.Aux)
                      (@List.nil.{0} NLogN.Item) →
                    @NLogN.IExec KoanaKPaths.Machine.Wedge.NS
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I KoanaKPaths.Machine.Wedge.prog
                      (@NLogN.IStmt.call KoanaKPaths.Machine.Wedge.NS
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (nat_lit 0))))
                      s
                      (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS
                        (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A ta)
                        KoanaKPaths.Machine.Wedge.R
                        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
                          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
                          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
                            (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs xs))
                          (@List.cons.{0} NLogN.Item NLogN.Item.mark
                            (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.R))))
                      (KoanaKPaths.Machine.Wedge.wedgeCost vs xs) := by sorry
