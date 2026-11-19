-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeReverse_width
-- name    : KoanaKPaths.Machine.Wedge.wedgeReverse_width
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:51.932209+00:00
-- url     : https://prove2.me/theorems/bb9e343d-1800-4141-b2a3-609ba96d0f57
-- title:
--   Linear growth of coordinate bit width under right multiplication by signs
-- statement:
--   Let $v$ be any finite list of signs and $X$ any integer list whose entries have absolute bit length at most $w$. Every entry $y$ produced by the recursive right-wedge block operation satisfies
--   $$\operatorname{bits}(y)\le w+|v|.$$
--   Here bits denotes the bit length of the absolute value, and the vector is stored in decreasing coordinate order for wedgeReverse. No length hypothesis on $X$ is required for this width bound. The operation is defined by taking lower and upper blocks and forming signed differences in the upper block. This lemma ensures that integer widths grow only linearly in the exterior dimension, allowing subsequent machine-cost bounds to charge actual bit arithmetic.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WedgeBounds.lean, line 43; source snapshot SHA-256 938783a813d86bb482c15a212a67d445900ed84c6c88f7c3f4e8952505d7fa0d.

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
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem KoanaKPaths.Machine.Wedge.wedgeReverse_width :
∀ (vs xs : List.{0} Int) (w : Nat)
  (hv :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
        Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (y : Int),
  @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
      (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs xs) y →
    @LE.le.{0} Nat instLENat (NLogN.zsz y)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int vs)) := by sorry
