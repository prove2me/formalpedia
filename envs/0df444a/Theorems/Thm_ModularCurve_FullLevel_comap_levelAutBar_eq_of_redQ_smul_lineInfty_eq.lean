-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
-- name    : ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/90d11e0b-b6b2-5fc8-8983-2f0cd20c86d2
-- title:
--   Borel-fixing level automorphisms preserve the Gauss valuation ring
-- statement:
--   Let $q\ge 5$ be a prime and $M'\ge 1$ an integer with $q\nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$ (the predicate `LiesOverPrime`), and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$. Write $F=$ `fieldBar q M'` for the intermediate field `xHFunctionFieldBar (q^2*M') (levelH q M')` of $\overline{\mathbb Q}((Q))$ over $\overline{\mathbb Q}$. Let $O$ be a valuation subring of $F$ satisfying the Gauss presentation condition: for $f\in F$, $f\in O$ if and only if there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ modulo the maximal ideal of $A$ is nonzero and $f$ times the image of $y$ in $\overline{\mathbb Q}((Q))$ equals the image of $x$. Let $\delta\in \mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and assume that the image `redQ q δ` of $\delta$ in $\mathrm{GL}_2(\mathbb Z/q)$ fixes the point `lineInfty q` $=[1:0]$ of $\mathbb P^1(\mathbb Z/q)$. Then the preimage of $O$ under the ring homomorphism underlying `levelAutBar q M' ζ δ` — the $\overline{\mathbb Q}$-algebra automorphism of $F$ chosen to satisfy the predicate `IsLevelAutBar q M' ζ δ` when such an automorphism exists, and the identity otherwise — is again $O$.
--
--   In classical terms, $O$ is the Gauss valuation ring attached to the $q$-expansion at the cusp $\infty$, the local ring of the generic point of the Igusa component through $\infty$ in the reduction at $q$ of the modular curve of level $\Gamma(q)\cap\Gamma_0(M')\cong\Gamma_H(q^2M')$, and the assertion is that the level automorphisms coming from matrices whose reduction mod $q$ lies in the upper-triangular Borel subgroup stabilise that component. It is used in the construction of the semistable covering of the full-level modular curve, in particular in the naturality statements for level automorphisms and in the criterion `comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hfix : redQ q δ • lineInfty q = lineInfty q) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O := by sorry
