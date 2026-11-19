-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
-- name    : KoanaKPaths.Machine.Arithmetic.Expr.compile_runs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:06.996209+00:00
-- url     : https://prove2.me/theorems/b42c9fac-7c19-4fec-9a4b-88f80ab6bf74
-- title:
--   Native compilation of bounded natural arithmetic expressions
-- statement:
--   Let $e$ be an expression built from natural constants, input variables, addition, and multiplication, with input values $v$. Each input register has its corresponding value at its head, and none is the evaluation register. Suppose every intermediate expression value has bit width at most $w$. Compiling and running $e$ prepends its exact value to the evaluation stack:
--   $$\operatorname{Eval}_{\rm after}=\operatorname{eval}(e,v)::\operatorname{Eval}_{\rm before},\qquad t\le 10000\,|e|(w+1)^2.$$
--   Here $|e|$ is the expression's syntactic size and $t$ is charged native bit time. All input registers, tails, input position, and output are preserved. The lemma supports arithmetic address and loop-control computations.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeExpressions.lean, line 42; source snapshot SHA-256 c5710d72f59873f78a8a866cf84a81d8abd384a759b5a710c8a73806766dec33.

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

theorem KoanaKPaths.Machine.Arithmetic.Expr.compile_runs :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Square.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Square.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (s : NLogN.IState KoanaKPaths.Machine.Square.NS)
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Arithmetic.Expr.compile v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e)))
        (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@KoanaKPaths.Machine.Arithmetic.Expr.size v e))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by sorry
