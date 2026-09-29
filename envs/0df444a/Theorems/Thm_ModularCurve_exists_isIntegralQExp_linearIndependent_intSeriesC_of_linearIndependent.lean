-- Prove2me | Theorems.Thm_ModularCurve_exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent
-- name    : ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/0566011d-5185-5697-bb3f-5132f5afe5dc
-- title:
--   Rank of an integral family survives reduction on Γ₁(M)
-- statement:
--   Let $\kappa$ be a field, let $M$ be a natural number, $k$ an integer and $d$ a natural number. Let $g : \mathrm{Fin}\,d \to$ the space of modular forms of weight $k$ for $\Gamma_1(M)$, and let $pg : \mathrm{Fin}\,d \to \mathbb{Z}[[q]]$ be integral power series such that for each $i$ the pair $(g_i, pg_i)$ satisfies `IsIntegralQExp`, i.e. the image of $pg_i$ under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ is exactly the $q$-expansion of width $1$ of $g_i$, and assume that the family $g$ is linearly independent over $\mathbb{C}$. The conclusion asserts the existence of a family $g' : \mathrm{Fin}\,d \to$ modular forms of weight $k$ for $\Gamma_1(M)$ together with integral power series $pg' : \mathrm{Fin}\,d \to \mathbb{Z}[[q]]$ such that again each $pg'_i$ maps to the width-$1$ $q$-expansion of $g'_i$, and such that the reductions $\mathrm{intSeriesC}\,\kappa\,(pg'_i)$ — the images of $pg'_i$ under coefficientwise reduction $\mathbb{Z} \to \kappa$, viewed inside the Laurent series field $\kappa((q))$ — form a family that is linearly independent over $\kappa$. No relation between $g'$ and the original family $g$ is asserted beyond the common index type $\mathrm{Fin}\,d$; in particular the statement does not claim that $g$ itself has independent reductions, only that some integral family of the same size does.
--
--   This is the 'reduction does not drop rank' step for $\Gamma_1(M)$: it converts a complex-linearly independent family of integral modular forms into one whose $q$-expansions stay independent after reduction to a field $\kappa$, so that dimension counts for holomorphic forms can be transferred to mod-$p$ coefficient fields. It feeds the comparison of such families across levels, [`ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_gamma1_of_le`](thm.html#ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_gamma1_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent
    (κ : Type) [Field κ] (M : ℕ) (k : ℤ) {d : ℕ}
    (g : Fin d → ModularForm (Gamma1 M) k) (pg : Fin d → PowerSeries ℤ)
    (hg : ∀ i, IsIntegralQExp (g i) (pg i)) (hli : LinearIndependent ℂ g) :
    ∃ (g' : Fin d → ModularForm (Gamma1 M) k) (pg' : Fin d → PowerSeries ℤ),
      (∀ i, IsIntegralQExp (g' i) (pg' i)) ∧ LinearIndependent κ (fun i => intSeriesC κ (pg' i)) := by sorry
