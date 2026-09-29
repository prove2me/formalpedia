-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two
-- name    : ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/1542efc6-b1cc-514d-9e7b-b53523e0a9f1
-- title:
--   Gauss-ring stability at ∞ forces the Borel condition (q=2)
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $(q : \overline{\mathbb{Q}})$ is a nonunit of $A$. Let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $O$ be a valuation subring of the field `fieldBar q M'`, the intermediate field $\overline{\mathbb{Q}}\cdot F(\Gamma_H(q^2M'))$ of $\overline{\mathbb{Q}}((q))$ obtained from `levelH q M'`, subject to the hypothesis that $f \in O$ holds exactly when there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to the residue field of $A$ is nonzero and $f \cdot y = x$ inside $\overline{\mathbb{Q}}((q))$. Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$, and suppose the pullback of $O$ along the ring homomorphism underlying the automorphism `levelAutBar q M' ζ δ` of `fieldBar q M'` over $\overline{\mathbb{Q}}$ is again $O$. Then the image `redQ q δ` of $\delta$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ fixes the point `lineInfty q` $= [1 : 0]$ of $\mathbb{P}^1(\mathbb{Z}/q)$.
--
--   This is the converse half of the statement that the Gauss valuation ring of the $q$-expansion at $\infty$ on the full-level function field is stabilised precisely by the Borel subgroup modulo $q$, here in the case $q = 2$; equivalently, stability of $O$ forces $q$ to divide the lower-left entry of $\delta$. It is used in the construction of the Igusa valuation subrings at $q = 2$ and in the counting bound [`ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem_of_eq_two`](thm.html#ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (h : O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O) :
    redQ q δ • lineInfty q = lineInfty q := by sorry
