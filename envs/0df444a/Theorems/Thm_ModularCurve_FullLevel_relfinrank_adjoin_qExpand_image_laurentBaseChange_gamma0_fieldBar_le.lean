-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le
-- name    : ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/01a7a5f7-0aa8-5cce-9684-5a1698679bce
-- title:
--   Relative degree at most q(q-1)/2 over the q-expanded Γ₀(qM) field
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let $M$ be a non-zero natural number with $q \nmid M$. All fields occur inside the Laurent series field $\overline{\mathbb Q}((t))$ over an algebraic closure of $\mathbb Q$. Write $F_{\mathbb Q}(\Gamma_0(qM)) =$ `qExpFunctionFieldC ℚ (Gamma0 (q * M))` for the subfield of $\mathbb Q((t))$ generated over $\mathbb Q$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions $p_f,p_g$ of two modular forms $f,g$ of one and the same weight on $\Gamma_0(qM)$ (with the denominator series non-zero), and let its base change $L =$ `laurentBaseChange (AlgebraicClosure ℚ) …` be the subfield of $\overline{\mathbb Q}((t))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of that field. Let `qExpand (AlgebraicClosure ℚ) q` be the ring homomorphism on Laurent series multiplying all exponents by $q$, i.e. the substitution $t \mapsto t^{q}$, and let $K_B$ be the subfield of $\overline{\mathbb Q}((t))$ generated over $\overline{\mathbb Q}$ by the image of $L$ under it. Finally let `fieldBar q M` be the base change to $\overline{\mathbb Q}$, in the same sense, of the field `xHFunctionField (q ^ 2 * M) (levelH q M)`, where `levelH q M` is the kernel of the reduction $(\mathbb Z/q^{2}M)^{\times} \to (\mathbb Z/q)^{\times}$, that is the subgroup of units congruent to $1$ modulo $q$. The assertion is that the relative degree `IntermediateField.relfinrank` of $K_B$ in `fieldBar q M` — the degree of `fieldBar q M` over its intersection with $K_B$, which is the degree $[\,$`fieldBar q M`$: K_B\,]$ once $K_B$ is contained in `fieldBar q M` — is at most $q(q-1)/2$.
--
--   This bounds the degree of the function field of one geometric component of the full level $q$ modular curve (with auxiliary $\Gamma_0(M)$-structure) over the subfield obtained from level $\Gamma_0(qM)$ by the substitution $t \mapsto t^{q}$, the field fixed by the Borel at $q$. It is used in the identification of that component's function field and of the associated Kummer generator, and in the computation of the comparison of level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel CongruenceSubgroup
open ModularCurve

theorem ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M : ℕ) [NeZero M] (hqM : ¬ q ∣ M) :
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
        (qExpand (AlgebraicClosure ℚ) q ''
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M))) :
            Set (LaurentSeries (AlgebraicClosure ℚ))))).relfinrank (fieldBar q M) ≤ q * (q - 1) / 2 := by sorry
