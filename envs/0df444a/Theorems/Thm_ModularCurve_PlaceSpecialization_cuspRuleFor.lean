-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_cuspRuleFor
-- name    : ModularCurve.PlaceSpecialization.cuspRuleFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7d0b0d31-d44e-54b0-98c2-69f134163a56
-- title:
--   Weak cusp rule for a place-specialization packet on X₀(p)
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, natural numbers $\ell$ and $p$ with $\ell$ prime, $p \neq 0$, $p$ prime and $\ell \neq p$; modular polynomial data `data` for $\ell$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ vanishing on the $q$-expansions $j(q)$, $j(q^\ell)$) satisfying the Kronecker congruence $\overline{\Phi} = (X^\ell - Y)(X - Y^\ell)$ modulo $\ell$; a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red} : A \to k$; hypotheses $h\alpha$, $h\beta$ that the two Hecke correspondence maps `heckeAlphaBar`, `heckeBetaBar` at level $p$ and index $\ell$ are integral; and a place-specialization packet $S$ for these data, together with any module structure over `HeckeAlg` $= \mathbb Z[X_q : q \text{ prime}]$ on $J_0(p) = \mathrm{Pic}^0$ of the modular function field of level $p$ over $\overline{\mathbb Q}$. Then the induced homomorphism `S.spPic0` from $J_0(p)$ to $\mathrm{Pic}^0$ of the level-$p$ modular function field over $k$ satisfies `CuspRuleFor A`: for every place $x$ of the base-changed modular function field and all $j_1, j_2 \in \overline{\mathbb Q}$ such that $x - \bar\infty$ and $x - \bar 0$ have degree zero, $x$ is fixed by the arithmetic Galois action of every $\sigma \in \mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$, $\mathrm{ord}_x(j - j_1) > 0$, $\mathrm{ord}_x(j_p - j_2) > 0$ and $|j_1|_A > 1$, one has: if $|j_2|_A = |j_1|_A^{\,p}$ then `S.spPic0` of the class of $x - \bar\infty$ lies in the subgroup `spKernelImage S.spPic0`, and if $|j_2|_A^{\,p} = |j_1|_A$ then `S.spPic0` of the class of $x - \bar 0$ lies in that same subgroup.
--
--   This is the weak, membership-shaped form of the cusp rule attached to a crossing place of $X_0(p)$ in the analysis of the cuspidal divisor classes, in the style of Mazur's study of the Eisenstein ideal. It is one of the conjuncts consumed by [`ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates`](thm.html#ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates) when assembling the package of predicates for a good-reduction specialization of $J_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_cuspRuleFor.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_StepThreeDoorPredicates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.PlaceSpecialization.cuspRuleFor
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ p : ℕ) [Fact ℓ.Prime] [NeZero p] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (S : ModularCurve.PlaceSpecialization A ℓ p data hKr k red hα hβ)
    [Module ModularCurve.HeckeAlg (ModularCurve.JZero p)] :
    ModularCurve.CuspRuleFor A S.spPic0 := by sorry
