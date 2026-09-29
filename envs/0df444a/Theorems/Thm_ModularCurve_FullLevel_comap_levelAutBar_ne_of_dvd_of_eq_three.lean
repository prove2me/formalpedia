-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_three
-- name    : ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/7d690116-a371-5aca-a14c-4c17e57f8e4c
-- title:
--   At full level q=3, an antipodal level automorphism moves the Gauss ring
-- statement:
--   Fix a prime $q$ together with the hypothesis $q = 3$, and a nonzero natural number $M'$ with $q \nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$, and let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$. Write $F =$ `fieldBar q M'` for the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained by base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $\Gamma_H(q^2M')$, where $H \le (\mathbb{Z}/q^2M')^\times$ is the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Let $O$ be a valuation subring of $F$ whose members are characterised as follows: $f \in O$ if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ along $A \to A/\mathfrak{m}_A$ is nonzero and $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$ (the Gauss valuation ring attached to $A$ and the $q$-expansion at $\infty$). Finally let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and have upper-left entry divisible by $q$. Then the preimage of $O$ under the ring homomorphism underlying the automorphism `levelAutBar q M' ζ δ` of $F$ over $\overline{\mathbb{Q}}$ is different from $O$. Here `levelAutBar q M' ζ δ` is an automorphism $\tau$ of $F$ over $\overline{\mathbb{Q}}$ chosen, if one exists, so that for every weight $k$, all modular forms $f, g$ on $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f, p_g$ and $p_g$ of nonzero associated series, and every embedding $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the image under $\iota$ of $\tau$ applied to the ratio of the $q$-expansions of $f$ and $g$, multiplied by the $q$-expansion of $g \mid_k \mathrm{conjElem}\,q\,\delta$, equals the $q$-expansion of $f \mid_k \mathrm{conjElem}\,q\,\delta$; if no such $\tau$ exists the identity is taken.
--
--   The statement records, in the case $q = 3$, that a level automorphism coming from a matrix of $\Gamma_0(M')$ with upper-left entry divisible by $q$ does not preserve the Gauss valuation ring of the $q$-expansion at the cusp $\infty$ of the full-level curve, i.e. that such a matrix moves that cusp. It is used in contrapositive form by [`ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three`](thm.html#ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three) in the analysis of the reduction at $q$ of the modular curve of level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom ≠ O := by sorry
