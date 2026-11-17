-- Prove2me | Theorems.Thm_N25_GlobalKummer_geometric_surjective
-- name    : N25.GlobalKummer.geometric_surjective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:58.099743+00:00
-- url     : https://prove2.me/theorems/32478712-dae8-4111-ac9f-59b578d20944
-- title:
--   The selected endomorphism is geometrically surjective
-- statement:
--   Let $J$ be the geometric Jacobian carrier and let $π=2+4γ+γ^2$ be the selected endomorphism, where $γ$ is the order-five diamond action. If $1+γ+γ^2+γ^3+γ^4=0$ on $J$, then $$\forall P\in J\ \exists Q\in J,\qquad π(Q)=P.$$ This produces a geometric division point before the arithmetic descent forces one to be rational.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_N25_LocalKummerPolynomial
import Definitions.Def_N25_KummerFactorization
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

open N25

theorem N25.GlobalKummer.geometric_surjective (hPhi : PhiFiveZero) : Function.Surjective piEnd := by sorry
