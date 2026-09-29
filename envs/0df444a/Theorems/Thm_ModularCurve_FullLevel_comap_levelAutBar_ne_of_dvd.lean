-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd
-- name    : ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/ea4f3c58-7f0e-5f19-808a-f120e2d363db
-- title:
--   Level automorphism with q ∣ δ₀₀ moves the Gauss ring
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$. Let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and write $F =$ `fieldBar q M'` for the compositum of $\overline{\mathbb{Q}}$ with the $q$-expansion function field of level $q^2M'$ and subgroup `levelH q M'` (the kernel of the reduction map on unit groups attached to the divisibility `dvd_sq_mul q M'`), realised inside $\overline{\mathbb{Q}}((q))$. Let $O$ be a valuation subring of $F$ which is assumed to be given in the Gauss presentation: $f \in O$ precisely when there are Laurent series $x, y$ with coefficients in $A$ such that the reduction of $y$ modulo the maximal ideal of $A$ is nonzero and $f \cdot y = x$ as Laurent series over $\overline{\mathbb{Q}}$. Finally let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and have upper-left entry divisible by $q$. Then the preimage of $O$ under the ring homomorphism underlying the automorphism `levelAutBar q M' ζ δ` of $F$ over $\overline{\mathbb{Q}}$ — the automorphism determined, when it exists, by the condition that on ratios of $q$-expansions of modular forms of level $\Gamma_H(q^2M')$ it implements the slash action by `conjElem q δ`, under any embedding of $\overline{\mathbb{Q}}$ into $\mathbb{C}$ carrying $\zeta$ to $e^{2\pi i/q}$ — is different from $O$.
--
--   This is the statement that a level automorphism coming from an element of $\Gamma_0(M')$ whose upper-left entry is divisible by $q$ does not fix the Gauss valuation ring of the cusp $\infty$ on the modular curve of level $q^2M'$, i.e. it carries that place to a different place. It is used in [`ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq`](thm.html#ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq) in the analysis of the mod $q$ reduction of the curve and of the Galois action on its components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom ≠ O := by sorry
