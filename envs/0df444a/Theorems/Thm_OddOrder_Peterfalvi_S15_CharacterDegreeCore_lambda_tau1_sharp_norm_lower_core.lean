-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_lambda_tau1_sharp_norm_lower_core
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.lambda_tau1_sharp_norm_lower_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:01:07.055503+00:00
-- url     : https://prove2.me/theorems/0009bba0-4ce7-445f-8914-732940c151b9
-- title:
--   Peterfalvi (13.6): lower bound $\sum_{H^\#}|\lambda^{\tau_1}|^2\ge |S|-\lambda(1)^2$ (Core form)
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G`, let `hyp : Hypothesis` be the Peterfalvi (13.1) configuration, and let a `LambdaClusterData hyp` (the $\lambda$-cluster, with character $\lambda=$ `lam.lambda`, a class function on $S$) and `core : CharacterDegreeCore hyp` (Core data providing the $\tau_1$-extension `core.tau1S`). Put $H=PC$ and $H^\#=H\setminus\{1\}$. Then
--
--   $$|S|-(uq)^2\ \le\ \sum_{x\in H^\#}\big|\lambda^{\tau_1}(x)\big|^2 ,\qquad \lambda^{\tau_1}=\text{`core.tau1S lam.lambda`}.$$
--
--   The estimate (13.6) feeds the constructed (13.5) correction package into the abstract Case B norm engine and is then compared with the $\eta$-grid bounds in Section 13.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/LambdaCorrection.lean#L503-L566

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped Classical in
open scoped FiniteInduce in

theorem CharacterDegreeCore.lambda_tau1_sharp_norm_lower_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    (Nat.card ↥hyp.S : ℝ) - ((hyp.u * hyp.q : ℕ) : ℝ) ^ 2
      ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset,
          ‖core.tau1S lam.lambda x‖ ^ 2 := by sorry

end

end OddOrder.Peterfalvi.S15
