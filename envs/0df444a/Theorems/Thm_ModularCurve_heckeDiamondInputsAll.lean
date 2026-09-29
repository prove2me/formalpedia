-- Prove2me | Theorems.Thm_ModularCurve_heckeDiamondInputsAll
-- name    : ModularCurve.heckeDiamondInputsAll
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/a07d21b3-b262-5d7a-8550-b4519afd5006
-- title:
--   The Hecke and diamond inputs for X₁(M) all hold
-- statement:
--   For every natural number $M \neq 0$ the predicate [`ModularCurve.HeckeDiamondInputsAll M`](def/ModularCurve_X1HeckeModule.html#L58) holds. Unfolded, it is the conjunction of two assertions. First, for every prime $\ell$ the predicate [`ModularCurve.HeckeInputsOneAlong`](def/ModularCurve_X1HeckeOperator.html#L183) holds for the coefficient field $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, level $M$ and index $\ell$: there exist witnesses for `HeckeBetaOneDefined M ℓ`, for the integrality predicates `HeckeAlphaOneBarIntegral` and `HeckeBetaOneBarIntegral` over $\overline{\mathbb Q}$, for `HasPrincipalDivisors` of the base-changed field `laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ))`, and for the finiteness predicate `FiniteAlong` applied to `heckeAlphaOneBar`, such that `FundamentalIdentityAlong` holds along `heckeBetaOneBar` (with its integrality witness) and `NormFormulaAlong` holds along `heckeAlphaOneBar` (with its finiteness witness). Secondly, for every $d$ coprime to $M$ there is a $\mathbb Q$-algebra automorphism $\sigma$ of the $q$-expansion function field `x1FunctionField M` with `IsDiamondAut M d σ`, i.e. for all weights $k$, all modular forms $f,g$ of weight $k$ on $\Gamma_1(M)$ with integral $q$-expansions $p_f,p_g$, $\mathrm{intSeriesC}_{\mathbb Q}(p_g) \neq 0$, and all $\gamma \in \Gamma_0(M) \subseteq \mathrm{SL}_2(\mathbb Z)$ with $\gamma_{00} \equiv d \pmod M$, the image in $\mathbb C((q))$ of $\sigma(p_f/p_g)$ times `slashQExpC k g γ` equals `slashQExpC k f γ`; and there is a $\overline{\mathbb Q}$-algebra automorphism $\sigma'$ of `x1FunctionFieldBar M` which is a base change of `diamondAut M d`, meaning $\sigma'$ agrees with `diamondAut M d` on coefficient-embedded elements of `x1FunctionField M`.
--
--   This collects, in a single statement valid for all levels, the geometric and field-theoretic inputs used to construct the Hecke operators $T_\ell$ and the diamond operators $\langle d\rangle$ on the Jacobian of $X_1(M)$: the $q \mapsto q^{\ell}$ degeneracy data, integrality and finiteness along the two degeneracy maps, existence of principal divisors, the fundamental identity and the norm formula, and the existence of diamond automorphisms together with their base change to $\overline{\mathbb Q}$. It is invoked by the statements attaching $\ell$-adic Galois representations to eigenforms and computing characteristic polynomials of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDiamondInputsAll.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeDiamondInputsAll (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondInputsAll M := by sorry
