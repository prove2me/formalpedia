-- Prove2me | Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
-- name    : ModularCurve.qExpand_mem_xHFunctionField_of_mem_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e36d67b3-bbe4-5ce2-933d-fb1cdb3e2b6c
-- title:
--   q↦ qᵖ sends the level M/p function field into level M
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$. Write $H' =$ `infSubgroup p M H hpM` for the image of $H$ under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ induced by $(M/p) \mid M$. Let $y$ be a Laurent series over $\mathbb{Q}$ lying in `xHFunctionField (M / p) H'`, that is, in the intermediate field `qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) H')` of $\mathbb{Q}((q))$ over $\mathbb{Q}$ attached to the congruence subgroup $\Gamma_{H'}(M/p) \le \mathrm{SL}_2(\mathbb{Z})$, which by definition is the subfield generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ (CohCarrier.GammaH (M / p) H')`. The conclusion is that the image of $y$ under the ring homomorphism `qExpand ℚ p`, which rescales the exponents of a Laurent series by the factor $p$ (so $q \mapsto q^{p}$, i.e. $y(q) \mapsto y(q^{p})$), lies in `xHFunctionField M H`, the corresponding intermediate field attached to $\Gamma_{H}(M)$.
--
--   This is the function-field form of the second degeneracy map $X_H(M) \to X_{H'}(M/p)$, realised on $q$-expansions by $q \mapsto q^{p}$. It is used in the construction of Hecke operators and of the maps between differentials at the two levels, and is cited by the full-level comparison results for `laurentBaseChange` of these function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.qExpand_mem_xHFunctionField_of_mem_div
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField (M / p) (infSubgroup p M H hpM)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    qExpand ℚ p y ∈ xHFunctionField M H := by sorry
