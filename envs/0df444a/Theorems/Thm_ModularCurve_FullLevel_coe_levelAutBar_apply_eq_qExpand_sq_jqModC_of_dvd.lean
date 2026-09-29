-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
-- name    : ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/48f05d1e-38be-5c4b-b825-5c45bad7ffae
-- title:
--   Level automorphism with q ∣ a sends j to j(q^{q^2})
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ (an element of `Idx q`, the primitive $q$-th roots of unity of `AlgebraicClosure ℚ`), and let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and satisfy $q \mid \delta_{0,0}$, the upper-left entry. Write $F =$ `fieldBar q M'` for the intermediate field between $\overline{\mathbb{Q}}$ and $\overline{\mathbb{Q}}((Q))$ obtained by base change to $\overline{\mathbb{Q}}$ of the function field of $X_H$ at level $q^2M'$, where $H =$ `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Let $x \in F$ be an element whose underlying Laurent series is `jqModC`, namely $Q^{-1}$ times the image of the integral power series $E_4^3 \cdot \eta^{-1}$-type numerator `jNum`, that is the $q$-expansion of the modular invariant $j$. Then the Laurent series underlying $(\mathrm{levelAutBar}\ q\ M'\ \zeta\, \delta)(x)$ — the $\overline{\mathbb{Q}}$-algebra automorphism of $F$ selected by the characterising $q$-expansion property `IsLevelAutBar` for the pair $(\zeta,\delta)$, the identity if no such automorphism exists — equals `qExpand` of exponent $q^2$ applied to `jqModC`, i.e. the series $j$ with $Q$ replaced by $Q^{q^2}$.
--
--   This is the computation of the image of the modular invariant $j$ under the level automorphism attached to $(\zeta,\delta)$ in the cell where $q$ divides the upper-left entry of $\delta$: there the conjugate $\mathrm{diag}(q,1)^{-1}\delta\,\mathrm{diag}(q,1)$ acts as $z \mapsto q^2 z$ up to $\mathrm{SL}_2(\mathbb{Z})$, so $j$ is sent to $j(q^2z)$. It is used, together with the companion computations in the other cells, by the results [`ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_ne_of_dvd) and its variants for $q = 2, 3$ to separate the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ((levelAutBar q M' ζ δ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) (jqModC (AlgebraicClosure ℚ)) := by sorry
