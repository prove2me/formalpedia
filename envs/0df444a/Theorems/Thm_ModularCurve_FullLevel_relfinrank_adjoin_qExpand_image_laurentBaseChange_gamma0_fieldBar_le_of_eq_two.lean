-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two
-- name    : ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/e26a633c-a662-526f-ac72-1260669df936
-- title:
--   Degree at most 2 at q=2 over the q-expanded Γ₀-field
-- statement:
--   Let $q$ be a natural number carrying a primality instance and assume $q=2$, and let $M$ be a nonzero natural number with $q \nmid M$. Work inside the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ over an algebraic closure of $\mathbb Q$. Let $F_{\mathbb Q}(\Gamma_0(qM)) =$ `qExpFunctionFieldC ℚ (Gamma0 (q*M))` be the subfield of $\mathrm{LaurentSeries}(\mathbb Q)$ generated over $\mathbb Q$ by the quotients $\iota(p_f)/\iota(p_g)$, where $f,g$ are modular forms of a common weight $k$ on $\Gamma_0(qM)$ (as a subgroup of $\mathrm{GL}_2(\mathbb R)$) with integral $q$-expansions $p_f, p_g$ and $\iota(p_g) \neq 0$; let $K_1 =$ `laurentBaseChange` of this field, i.e. the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of $F_{\mathbb Q}(\Gamma_0(qM))$ under $\mathbb Q \to \overline{\mathbb Q}$. Let $A$ be the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ generated over $\overline{\mathbb Q}$ by the image of $K_1$ under `qExpand`, the ring homomorphism multiplying all exponents by $q$ (substitution $t \mapsto t^q$). Finally `fieldBar q M` is the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image of `xHFunctionField (q^2*M) (levelH q M)`, the function field at level $q^2M$ with subgroup `levelH q M` the kernel of the reduction $(\mathbb Z/q^2M)^\times \to (\mathbb Z/q)^\times$. The assertion is that `IntermediateField.relfinrank` of $A$ relative to `fieldBar q M`, that is the degree of `fieldBar q M` over the intersection of the two fields, is at most $2$.
--
--   This is the $q=2$ instance of the bound on the degree of the full-level function field over the subfield obtained from level $\Gamma_0(qM)$ by the substitution $t \mapsto t^q$; at $q=2$ the group `levelH q M` is all of $(\mathbb Z/4M)^\times$, so the bound is $2$ rather than the value $q(q-1)/2$ occurring for larger primes. It feeds [`ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two`](thm.html#ModularCurve.FullLevel.adjoin_qExpand_image_le_fieldBar_and_relfinrank_pos_and_le_of_eq_two), where the inclusion $A \subseteq$ `fieldBar q M` and positivity of the relative degree are combined with it, and thence the identification of automorphisms at full level in [`ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel CongruenceSubgroup
open ModularCurve

theorem ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M : ℕ) [NeZero M] (hqM : ¬ q ∣ M) :
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M))) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M) ≤ 2 := by sorry
