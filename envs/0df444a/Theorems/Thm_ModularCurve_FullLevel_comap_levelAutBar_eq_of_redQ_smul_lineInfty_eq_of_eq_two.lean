-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
-- name    : ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/3359a26d-eabf-5e52-b83a-24bf38b75e69
-- title:
--   Borel-fixed level automorphisms preserve the Gauss ring, q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a nonunit of $A$. Let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $O$ be a valuation subring of the field `fieldBar q M'`, the intermediate field `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')` of $\overline{\mathbb{Q}}$-Laurent series, assumed to be given by the Gauss condition: an element $f$ lies in $O$ if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to the residue field of $A$ is nonzero and $f$ times the image of $y$ in $\overline{\mathbb{Q}}((X))$ equals the image of $x$. Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ belong to $\Gamma_0(M')$, and assume that the image `redQ q δ` of $\delta$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ fixes the point `lineInfty q` $= [1:0]$ of $\mathbb{P}^1(\mathbb{Z}/q)$. Then the preimage of $O$ under the ring homomorphism underlying `levelAutBar q M' ζ δ` — the chosen $\overline{\mathbb{Q}}$-algebra automorphism of `fieldBar q M'` satisfying `IsLevelAutBar q M' ζ δ` if such an automorphism exists, and the identity otherwise — is again $O$.
--
--   This is the case $q = 2$ of the stability, under the level automorphisms attached to elements of $\Gamma_0(M')$ whose reduction fixes the cusp $\infty$, of the Gauss valuation ring cut out on the function field of a component of the modular curve of level $K(q)K_0(M')$ by the $q$-expansion at $\infty$. It feeds the naturality statements for the semistable covering of that modular curve and the identification of the ring of integers at $\infty$ as an Igusa ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hfix : redQ q δ • lineInfty q = lineInfty q) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O := by sorry
