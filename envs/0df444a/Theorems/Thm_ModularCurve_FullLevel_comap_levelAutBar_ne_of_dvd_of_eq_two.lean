-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two
-- name    : ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/dc06471e-61f4-51f0-8fd6-d2c04175dd4c
-- title:
--   A level automorphism at q=2 moves the Gauss ring
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to the nonunits of $A$. Let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Write $F =$ `fieldBar q M'` for the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained by base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of level $\Gamma_H(q^2M')$, where $H$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $O$ be a valuation subring of $F$ which is assumed to be given by the Gauss presentation: for $f \in F$, $f \in O$ if and only if there are Laurent series $x, y$ over $A$ such that the coefficientwise reduction of $y$ modulo the maximal ideal of $A$ is nonzero and $f \cdot y = x$ inside $\overline{\mathbb{Q}}((q))$. Finally let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and have upper-left entry divisible by $q$. Then the preimage of $O$ under the ring homomorphism underlying the $\overline{\mathbb{Q}}$-algebra automorphism `levelAutBar q M' ζ δ` of $F$ is different from $O$; here `levelAutBar q M' ζ δ` is the automorphism of $F$ chosen to satisfy the $q$-expansion condition `IsLevelAutBar q M' ζ δ`, relating $\tau$ applied to ratios of integral $q$-expansions of weight-$k$ forms on $\Gamma_H(q^2M')$ to the ratio of the $q$-expansions of their translates by `conjElem q δ` (and taken to be the identity if no such automorphism exists).
--
--   This is the case $q = 2$ of the assertion that an element $\delta$ of $\Gamma_0(M')$ whose upper-left entry is divisible by $q$ carries the Gauss valuation ring of the cusp at infinity to a different valuation ring, so that the induced automorphism does not fix the component of the reduction of the modular curve through $\infty$. It is used by [`ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two`](thm.html#ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two) in the analysis of the action of level structures on the components of the reduction modulo $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom ≠ O := by sorry
