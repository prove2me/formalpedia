-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Trial_signAddress_runs
-- name    : KoanaKPaths.Machine.Trial.signAddress_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:21:34.841875+00:00
-- url     : https://prove2.me/theorems/b9d40da4-8084-4f78-9197-41145e08f33b
-- title:
--   Translate a logical sign address into the reversed-cache address
-- statement:
--   Let $e$ be a nonnegative arithmetic expression over natural input values held in native registers distinct from the evaluation register. Suppose the total sign count is $T$, its width and every intermediate expression width are at most $w\ge1$, and $j=e(\mathbf x)<T$. The sign-address program prepends to the binary-index source register
--   $$
--   i=T-1-j,
--   $$
--   changing only that source register and preserving every other register and saved tail. Its charged running time is at most
--   $$
--   30000(|e|+2)(w+1)^2,
--   $$
--   where $|e|$ is the expression-tree node count. The subtraction is natural subtraction and agrees here with integer subtraction because $j<T$. This is the interface between logical label/sketch coordinates and the physical reverse-ordered shared sign cache.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/SignAddress.lean, line 21; source snapshot SHA-256 9f8220eb5419d1a28007a7de039fcc2e02dfe0d69fe8035a1e3c98f53dc76f03.

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

theorem KoanaKPaths.Machine.Trial.signAddress_runs :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Trial.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Trial.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (T w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (he : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (hT : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt T)) w)
  (hj : @LT.lt.{0} Nat instLTNat (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) T)
  (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (tt : List.{0} NLogN.Item)
  (hTotal :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt T)) tt))
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Trial.signAddress v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) T
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Source)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 30000) (instOfNatNat (nat_lit 30000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by sorry
