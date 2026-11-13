-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_G0_nonvanishing_dichotomy_core
-- name    : OddOrder.Peterfalvi.S15.CharacterDegreeCore.G0_nonvanishing_dichotomy_core
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:00:54.767542+00:00
-- url     : https://prove2.me/theorems/3f26f412-0b85-4093-b3a5-f549fd4ea85d
-- title:
--   Peterfalvi (13.9.a): $\lambda^{\tau_1}$ and $\eta_{10}$ do not vanish simultaneously on $G_0$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order, `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package, `core : CharacterDegreeCore hyp` the Core character-degree data and `lam : LambdaClusterData hyp` the $\lambda$-cluster data. Then for every $x\in G_0$ (`hyp.G0Finset`),
--   $$\lambda^{\tau_1}(x)\neq0\quad\text{or}\quad\eta_{10}(x)\neq0,$$
--   where $\lambda^{\tau_1}=$ `core.tau1S lam.lambda` and $\eta_{10}=$ `hyp.eta10`.
--
--   This is Peterfalvi (13.9.a), proved from the Core off-$H^\#$ formula, the regular value formula, and the four-corner grid relation.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean#L335-L442

import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

theorem CharacterDegreeCore.G0_nonvanishing_dichotomy_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    ∀ x ∈ hyp.G0Finset, core.tau1S lam.lambda x ≠ 0 ∨ hyp.eta10 x ≠ 0 := by sorry

end

end OddOrder.Peterfalvi.S15
