-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_Square_binaryAdd_exec
-- name    : KoanaKPaths.Machine.Square.binaryAdd_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:11.251183+00:00
-- url     : https://prove2.me/theorems/999651e9-c7b2-437d-9a62-a36eb7ecec5f
-- title:
--   Add the top two native evaluation integers with exact cost
-- statement:
--   Suppose the evaluation stack begins with integers $y,x$, followed by an arbitrary tail. The binary-add program consumes these two items and replaces them by their sum:
--   $$
--   [y,x]\mathbin{+\!+}\mathrm{tail}\quad\longmapsto\quad[x+y]\mathbin{+\!+}\mathrm{tail}.
--   $$
--   It preserves every other stack and the input/output state. Write $\beta(z)$ for the native integer width, $\mu$ for its integer-move charge, and $\alpha$ for its integer-addition charge. The execution has exact cost
--   $$
--   2\mu(\beta(y))+19+\alpha(\beta(x)+\beta(y)).
--   $$
--   The operands may have either sign and no numerical bound is assumed. This elementary contract lets arithmetic-expression and estimator proofs account for addition on actual encoded integers rather than unit-cost arithmetic.
-- source:
--   T. Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, October 2026, §3.2 (printed pp. 8–9 / PDF pp. 9–10) and §4.1 (printed p. 9 / PDF p. 10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf. Native implementation: Solutions/NativeBinary.lean, line 15; source snapshot SHA-256 b51823b641679c2e062fb551d102af66d11468643da3065d3a73c6d7e3675c49.

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

theorem KoanaKPaths.Machine.Square.binaryAdd_exec :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Square.NS) (x y : Int) (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int y) (@List.cons.{0} NLogN.Item (NLogN.Item.int x) tail))),
  @NLogN.IExec KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Square.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Square.binaryAdd s
    (@NLogN.IState.upd KoanaKPaths.Machine.Square.NS s KoanaKPaths.Machine.Square.Eval
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y))
        tail))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (NLogN.moveCost (NLogN.zsz y)))
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      (NLogN.addIntCost (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (NLogN.zsz x) (NLogN.zsz y)))) := by sorry
