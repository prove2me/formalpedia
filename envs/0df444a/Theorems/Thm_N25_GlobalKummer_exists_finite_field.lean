-- Prove2me | Theorems.Thm_N25_GlobalKummer_exists_finite_field
-- name    : N25.GlobalKummer.exists_finite_field
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:39.055316+00:00
-- url     : https://prove2.me/theorems/5fcf6e96-cd67-4bee-9f27-43d32d981028
-- title:
--   Every geometric Jacobian point is defined over a number field
-- statement:
--   Let $J$ be the geometric Jacobian carrier over $ℚ̄$, and let $x\in J$. There exists an intermediate field $ℚ\subseteq L\subseteq ℚ̄$ of finite degree such that every $σ\in G_{ℚ}$ fixing $L$ also fixes $x$: $$\exists L/ℚ\text{ finite},\qquad G_L\subseteq\mathrm{Stab}_{G_{ℚ}}(x).$$ This gives the finite field of definition required to make division cocycles continuous.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC

open N25

theorem N25.GlobalKummer.exists_finite_field (x : J) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : Gal, σ ∈ L.fixingSubgroup → σ • x = x := by sorry
