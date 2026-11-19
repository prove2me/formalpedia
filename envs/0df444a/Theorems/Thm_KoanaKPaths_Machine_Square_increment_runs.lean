-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
-- name    : KoanaKPaths.Machine.Square.increment_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:16:15.538406+00:00
-- url     : https://prove2.me/theorems/bae77006-baa0-40ec-8205-740f8cedd5c7
-- title:
--   Incrementing a natural integer register with explicit bit cost
-- statement:
--   Let a native register $i$, distinct from the expression-evaluation register, begin with a natural number $n$. Assume $w\ge1$ and that the absolute bit length of $n$ is at most $w$. The native increment program replaces only this head by $n+1$:
--   $$i:n::T\longmapsto(n+1)::T,\qquad t\le13000(w+1)^2.$$
--   All original register tails, other registers, input position, and output are preserved. The increment is implemented by the bit-charged native arithmetic operations. This provides a uniform counter-update contract for graph vertices, sketch states, and layer indices, whose binary representations cannot be treated as unit-cost words.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeIncrement.lean, line 13; source snapshot SHA-256 592a44e1ac59208ba9cd6b225ac51c1b334c126d396e114942c6f457a91ff622.

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

theorem KoanaKPaths.Machine.Square.increment_runs :
∀ (I : List.{0} NLogN.Sym) (i : Fin KoanaKPaths.Machine.Square.NS)
  (hi : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) i KoanaKPaths.Machine.Square.Eval)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (n w : Nat) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s i)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) tail))
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hn : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt n)) w),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.Square.increment i) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s i
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        tail))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 13000) (instOfNatNat (nat_lit 13000)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by sorry
