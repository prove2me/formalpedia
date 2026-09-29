-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionSheaf_h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionSheaf.h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a0e1872b-7876-5d65-8ef3-ae38e1e206ec
-- title:
--   Two-adic bound h¹+a≤ h⁰+δ from non-empty flags
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ together with the hypothesis `hA` that $p$ lies in the non-units of $A$ (so $A$ lies over $p$), and let $S$ be a datum of type `JZeroNeronPrimaryTorsionSheaf p 2 A hA`: a core consisting of fppf sheaves $\mathcal{J}(m)$ of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb{Z}$, flat finite-type $\mathbb{Z}$-Hopf algebras $H(m)$ whose $\mathbb{Z}$-algebra homomorphisms into sections compute the sections of $\mathcal{J}(m)$, with generic points identified Galois-equivariantly with the Eisenstein $2$-power torsion subgroup $\mathrm{eisensteinPrimaryTorsionBar}\,p\,2\,m$ of $\mathrm{JZero}\,p$, points over $A$ identified with the toric Eisenstein $2$-primary part, short exact sequences $0\to\mathcal{J}(m)\to\mathcal{J}(m+1)\to Q(m)\to 0$ and Kummer rows; finite-flat models at the primes $\ell\ne p$ together with their reduction at $2$; and invariant pins, i.e. admissible invariants $\mathrm{inv}(m)$ at $q=2$ whose components satisfy $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mathcal{J}(m))=2^{h^0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb{Z},\mathcal{J}(m))=2^{h^1}$, $\#\mathrm{eisensteinPrimaryTorsionBar}\,p\,2\,m=2^{\delta}\cdot\#(\text{toric part})$, and the pin for $\alpha$. Assume further that for every $m$ the type `JZeroNeronPrimaryTorsionFlag p 2 A hA S.core m` of flags on $S$'s core at level $m$ is non-empty. The conclusion is that for every level $m$ and every natural number $a$ with $\#(H(m)\to_{\mathbb{Z}\text{-alg}}\overline{\mathbb{F}_2})=2^{a}$, the inequality $h^1(\mathrm{inv}(m))+a\le h^0(\mathrm{inv}(m))+\delta(\mathrm{inv}(m))$ holds in $\mathbb{Z}$.
--
--   This is the $q=2$ case of the numerical inequality underlying Mazur's count of Eisenstein torsion on $J_0(p)$ (Proposition 17 of the Eisenstein ideal paper), expressed for the Néron $2$-primary torsion sheaf data and its pinned invariants $h^0$, $h^1$, $\delta$. It is the inductive input to [`ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two), and is obtained by telescoping the flag filtration, using the step inequality for cokernels and the rigidity of finite flat Hopf algebras with a unique $\overline{\mathbb{Q}}$-point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionSheaf_h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionSheaf.h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p 2 A hA)
    (hflag : ∀ m, Nonempty (JZeroNeronPrimaryTorsionFlag p 2 A hA S.core m)) :
    ∀ m : ℕ, ∀ a : ℕ,
      Nat.card (S.core.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a →
      ((S.invPins.inv m).h1 : ℤ) + (a : ℤ) ≤ ((S.invPins.inv m).h0 : ℤ) + ((S.invPins.inv m).δ : ℤ) := by sorry
