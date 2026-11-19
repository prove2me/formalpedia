-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
-- name    : KoanaKPaths.Machine.Arithmetic.Expr.width_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:49.989193+00:00
-- url     : https://prove2.me/theorems/2f906e0a-40ba-45db-9773-c4f405eb7d28
-- title:
--   Bound every intermediate width in a nonnegative arithmetic expression
-- statement:
--   Consider an arithmetic expression $e$ built from nonnegative constants, nonnegative input values, addition and multiplication. Assume every constant and input appearing in $e$ has integer width at most $U$. Let $|e|$ be the number of syntax-tree nodes and let $\operatorname{width}(e)$ be the largest bit width among the values of all its subexpressions. Then
--   $$
--   \operatorname{width}(e)\le |e|(U+1).
--   $$
--   The width convention is the machine's signed-integer magnitude width, including its value at zero. The estimate controls intermediate arithmetic as well as the final value, so it can be passed to the native expression evaluator's bit-time bound. In particular, a short arithmetic address expression cannot conceal an unbounded intermediate integer when its atoms are width-bounded.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/ExpressionBounds.lean, line 14; source snapshot SHA-256 13c55bacb0880caf7c8435727b24bdd9a4d19712c972b84a2ad5d9c53790e187.

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

theorem KoanaKPaths.Machine.Arithmetic.Expr.width_le :
∀ {v : Nat} (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (U : Nat)
  (hw : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.atomWidth v values e) U),
  @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by sorry
