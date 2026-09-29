-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq
-- name    : ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/dac1fb8b-5b72-550a-8c71-0bed745bd0f4
-- title:
--   Level-automorphism invariants are Γ₀(M')-expansions in q^q
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $\bar F =$ `fieldBar q M'` for the intermediate field of $\overline{\mathbb{Q}}(\!(q)\!)$ over $\overline{\mathbb{Q}}$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the field `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $x \in \bar F$ be such that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ the automorphism `levelAutBar q M' ζ γ` of $\bar F$ over $\overline{\mathbb{Q}}$ — the chosen automorphism satisfying `IsLevelAutBar`, which compares, after any embedding $\overline{\mathbb{Q}} \hookrightarrow \mathbb{C}$ sending $\zeta$ to $e^{2\pi i/q}$, its value on a ratio of integral $q$-expansions of two modular forms of equal weight for $\Gamma_H(q^2M')$ with the corresponding ratio of the $q$-expansions of those forms translated by `conjElem q γ` — fixes $x$. Then there is a Laurent series $g$ lying in `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))`, the field generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of ratios $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_0(M')$, such that $x$, regarded as an element of $\overline{\mathbb{Q}}(\!(q)\!)$, equals `qExpand (AlgebraicClosure ℚ) q g`, the series obtained from $g$ by multiplying every exponent by $q$.
--
--   This is the classical identification of the invariants of the group of level automorphisms $\{\tau_\gamma : \gamma \in \Gamma_0(M')\}$ acting on the full-level-$q$ function field: an invariant element is a $\Gamma_0(M')$-modular function read in the variable $q^q$, that is, $x(z) = g(qz)$. It is used in the determination of the ring of integral elements, [`ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem`](thm.html#ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (x : fieldBar q M')
    (hx : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ x = x) :
    ∃ g : LaurentSeries (AlgebraicClosure ℚ),
      g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) ∧
      (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g := by sorry
