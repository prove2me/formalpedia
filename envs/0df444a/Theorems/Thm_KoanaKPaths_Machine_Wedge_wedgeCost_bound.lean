-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeCost_bound
-- name    : KoanaKPaths.Machine.Wedge.wedgeCost_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:28.73078+00:00
-- url     : https://prove2.me/theorems/7fce7565-aa67-48dc-b60a-565cdda9d618
-- title:
--   Singly exponential cost bound for recursive exterior multiplication
-- statement:
--   Let $\mathbf v$ be a length-$d$ vector of signs and $X$ an integer coefficient array of length $2^d$. Assume every input coefficient has native integer width at most $w$. The declared exact cost of the recursive wedge-coordinate computation satisfies
--   $$
--   C_{\wedge}(\mathbf v,X)\le100000(d+1)2^d(w+d+1).
--   $$
--   The vector entries must be $1$ or $-1$; no nonnegativity is required of $X$. The algorithm splits the subset-coordinate array into two half-size blocks, recurses on them and reconstructs the exterior product by signed additions and array transfers. This bound demonstrates that multiplication by a single vector takes a polynomial factor times $2^d$ charged steps, rather than a general $4^d$ exterior-algebra product.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/WedgeBounds.lean, line 196; source snapshot SHA-256 938783a813d86bb482c15a212a67d445900ed84c6c88f7c3f4e8952505d7fa0d.

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

theorem KoanaKPaths.Machine.Wedge.wedgeCost_bound :
∀ (vs xs : List.{0} Int) (w : Nat)
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)))
  (hv :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
        Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @LE.le.{0} Nat instLENat (KoanaKPaths.Machine.Wedge.wedgeCost vs xs)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 100000) (instOfNatNat (nat_lit 100000)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int vs)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int vs))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by sorry
