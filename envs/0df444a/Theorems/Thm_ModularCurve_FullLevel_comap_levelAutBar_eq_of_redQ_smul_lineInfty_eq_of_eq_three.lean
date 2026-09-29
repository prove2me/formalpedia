-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three
-- name    : ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/0dcca9d4-5092-5559-85cd-6367ed4c320c
-- title:
--   Gauss ring at ∞ is stable under Borel level automorphisms, q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number not divisible by $q$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ (the predicate `LiesOverPrime`, i.e. $(q : \overline{\mathbb{Q}}) \in A.\mathrm{nonunits}$), and let $\zeta$ be an element of `Idx q`, the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$. Let $O$ be a valuation subring of the field `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, an intermediate field between $\overline{\mathbb{Q}}$ and $\overline{\mathbb{Q}}((t))$, and assume $O$ is given by the Gauss presentation: an element $f$ lies in $O$ exactly when there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to the residue field of $A$ is nonzero and $f \cdot y = x$ inside $\overline{\mathbb{Q}}((t))$ (coefficients of $x,y$ pushed forward along the inclusion of $A$). Let $\delta \in \Gamma_0(M') \subseteq \mathrm{SL}_2(\mathbb{Z})$ be such that its reduction `redQ q δ` in $\mathrm{GL}_2(\mathbb{Z}/q)$ fixes the point `lineInfty q` $= [1:0]$ of the projective line over $\mathbb{Z}/q$. Then the preimage of $O$ under the ring homomorphism underlying `levelAutBar q M' ζ δ` — the chosen $\overline{\mathbb{Q}}$-algebra automorphism of `fieldBar q M'` satisfying the predicate `IsLevelAutBar q M' ζ δ`, the identity if no such automorphism exists — is again $O$.
--
--   This is the stability, under the level automorphisms attached to matrices in the Borel-type subgroup fixing the cusp $\infty$, of the Gauss valuation ring at $\infty$ on the function field of a component of the modular curve of level $K(q)K_0(M')$, in the case $q = 3$ (the companion of the statements for $q \ge 5$ and $q = 2$). It feeds the construction of the semistable covering of the full-level modular curve, being used in the naturality statements for the anchor and supersingular charts and in the identification of the integers at $\infty$ with an Igusa ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hfix : redQ q δ • lineInfty q = lineInfty q) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O := by sorry
