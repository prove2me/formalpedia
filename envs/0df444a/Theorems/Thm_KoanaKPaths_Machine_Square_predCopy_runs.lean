-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Square_predCopy_runs
-- name    : KoanaKPaths.Machine.Square.predCopy_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:12:20.538875+00:00
-- url     : https://prove2.me/theorems/d1ccded8-219d-4321-b65c-73d588d84250
-- title:
--   Copy the truncated predecessor of a native natural integer
-- statement:
--   Let the source register contain a natural number $n$ above its saved tail, with integer width at most $w\ge1$. Assume both source and destination registers are distinct from the evaluation scratch register; the source and destination themselves may coincide. The predecessor-copy program prepends the natural truncated predecessor to the destination:
--   $$
--   \operatorname{dst}_{\rm final}=\bigl[\max(n-1,0)\bigr]\mathbin{+\!+}\operatorname{dst}_{\rm initial}.
--   $$
--   Every other register is preserved, including the source when it differs from the destination. The evaluation scratch stack is restored, and the charged running time is at most
--   $$
--   12000(w+1)^2.
--   $$
--   This operation supports safe index and loop-bound calculations without introducing a negative integer when the input is zero.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativePredecessor.lean, line 14; source snapshot SHA-256 903ac618ee3db8cb847c7b1cd631cf4c7f2c246968d663ae9d2f6706c35f58e6.

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

theorem KoanaKPaths.Machine.Square.predCopy_runs :
∀ (I : List.{0} NLogN.Sym) (src dst : Fin KoanaKPaths.Machine.Square.NS)
  (hs : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) src KoanaKPaths.Machine.Square.Eval)
  (hd : @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) dst KoanaKPaths.Machine.Square.Eval)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (n w : Nat) (tail : List.{0} NLogN.Item)
  (hn :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s src)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) tail))
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (hb : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt n)) w),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.Square.predCopy src dst) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s dst
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s dst)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 12000) (instOfNatNat (nat_lit 12000)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by sorry
