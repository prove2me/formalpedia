-- Prove2me | Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
-- name    : ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/837f5903-b685-567c-8e7c-1162132ceb12
-- title:
--   Galois and Hecke actions on J₀(N) commute
-- statement:
--   Fix $N\ge 1$ (a natural number with `NeZero N`) and write $J_0(N)$ for the project's [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), namely the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` of the modular function field `modularFunctionFieldFull N` inside Laurent series; it carries the `DistribMulAction` of the group $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ obtained from the semilinear action on Laurent coefficients. The hypothesis `hcomm` is the project's predicate [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25), which says that for all primes $\ell,\ell'$ the endomorphisms `heckeOperatorBar N ℓ` and `heckeOperatorBar N ℓ'` of $J_0(N)$ commute; here `heckeOperatorBar N ℓ` is the $\mathbb{Z}$-linear map underlying `heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ`, the correspondence $\alpha_*\circ\beta^*$ on $\mathrm{Pic}^0$ attached to the two degeneracy maps of level $N\ell$, which by definition is the zero map whenever the package of integrality, principal-divisor, fundamental-identity, finiteness and norm-formula inputs `HeckeInputsAlong` fails. Under this hypothesis the statement asserts, for the module structure `heckeModuleBar N` of the polynomial Hecke algebra $\mathbb{T}=$ `HeckeAlg` $=\mathbb{Z}[X_\ell:\ell\ \text{prime}]$ on $J_0(N)$ introduced by `letI`, the instance `SMulCommClass`: for every $\sigma\in\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$, every $T\in\mathbb{T}$ and every $x\in J_0(N)$ one has $\sigma\cdot(T\cdot x)=T\cdot(\sigma\cdot x)$. Note that `heckeModuleBar N` is defined by a case distinction and only agrees with the correspondence action $X_\ell\cdot x=$ `heckeOperatorBar N ℓ x` when `hcomm` holds, which is exactly the situation assumed.
--
--   Classically this is the statement that $J_0(N)$ is a module over $\mathbb{T}[\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})]$: the Hecke correspondences are defined over $\mathbb{Q}$, hence commute with the Galois action on $\overline{\mathbb{Q}}$-points. The formal version differs from the textbook one in that the Hecke action is the total function `heckeModuleBar N`, defined by a case split and equal to the divisorial action only under the commutation hypothesis `hcomm`, and in that each individual Hecke correspondence is itself defined conditionally on its construction inputs. The resulting `SMulCommClass` instance is what discharges the corresponding section variable of the Eichler–Shimura and specialisation machinery, and it is invoked in the statements about semistable specialisation of $J_0(N)$, the Čerednik–Drinfel'd comparison, and the construction of Hecke eigenplanes in Tate modules of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar (N : ℕ) [NeZero N] (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) : letI := ModularCurve.heckeModuleBar N; SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg (ModularCurve.JZero N) := by sorry
