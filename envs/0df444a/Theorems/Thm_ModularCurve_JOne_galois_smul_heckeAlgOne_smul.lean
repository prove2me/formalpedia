-- Prove2me | Theorems.Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul
-- name    : ModularCurve.JOne.galois_smul_heckeAlgOne_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/b3305353-a583-5a5e-ac45-d6a8d26f470d
-- title:
--   Galois action on J₁(M) commutes with the Hecke action
-- statement:
--   Fix a natural number $M \neq 0$. Let $\sigma$ be an automorphism of $\mathrm{AlgebraicClosure}(\mathbb{Q})$ as a $\mathbb{Q}$-algebra, let $t$ be an element of [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16), the polynomial ring $\mathbb{Z}[X_i]$ on the index set $\mathrm{Primes} \sqcup \mathbb{N}$, and let $x$ be an element of [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), that is, of the degree-zero divisor class group $\mathrm{Pic}^0$ of the intermediate field `x1FunctionFieldBar M` (the base change to $\mathrm{AlgebraicClosure}(\mathbb{Q})$ of the function field `x1FunctionField M` inside the Laurent series field $\mathrm{AlgebraicClosure}(\mathbb{Q})((q))$), formed as the quotient of the group of degree-zero divisors by the subgroup of principal divisors. The group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acts on `JOne M` through the distributive action coming from its coefficientwise action, and the action of $t$ is taken with respect to the module structure [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129): this is defined by cases, namely by the ring homomorphism `heckeEvalOneBar` from `HeckeAlgOne` to $\mathrm{End}_{\mathbb{Z}}(\mathrm{JOne}\,M)$ when the generators `heckeDiamondGenBar M i` commute pairwise (the predicate `HeckeDiamondCommuteBar M`), and otherwise by evaluating all variables at $0$. The assertion is the unconditional identity $\sigma \bullet (t \bullet x) = t \bullet (\sigma \bullet x)$.
--
--   This is the statement that the Hecke operators and diamond operators on the Jacobian of $X_1(M)$, in its $q$-expansion model, are defined over $\mathbb{Q}$ and hence commute with the Galois action on $J_1(M)(\overline{\mathbb{Q}})$. It underlies the compatibility of the Galois representations attached to Hecke eigenclasses with the Hecke action, and is used in the analysis of Frobenius and inertia on the Tate modules of $J_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.galois_smul_heckeAlgOne_smul (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x) := by sorry
