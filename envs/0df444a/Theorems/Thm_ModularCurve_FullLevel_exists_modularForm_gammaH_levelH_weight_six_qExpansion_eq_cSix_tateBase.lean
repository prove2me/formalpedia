-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/b8f461f6-a594-554a-84c1-0a12a0dea818
-- title:
--   Weight-six form with q-expansion c₆ of Tate(q^{ q})
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, let $L$ be a field of characteristic zero and let $\iota : L \to \mathbb{C}$ be a ring homomorphism. Write $H_q \le (\mathbb{Z}/q^2M')^{\times}$ for the kernel of the reduction $(\mathbb{Z}/q^2M')^{\times} \to (\mathbb{Z}/q)^{\times}$ (the group [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22)), and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be [`CohCarrier.GammaH (q^2M') H_q`](def/CohCarrier_Level.html#L133), i.e. the matrices in $\Gamma_0(q^2M')$ whose lower-right entry has image in $H_q$ under [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121), viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. The assertion is the existence of a modular form $C_6$ of weight $6$ on $\Gamma$ such that, first, the $q$-expansion of $C_6$ with width $1$, regarded as a Laurent series over $\mathbb{C}$, coincides with the coefficientwise image under $\iota$ of the invariant $c_6$ of [`ModularCurve.tateBase L q`](def/ModularCurve_TateSlots.html#L46), the Tate Weierstrass curve over $L$-Laurent series pushed forward along the substitution $\mathfrak q \mapsto \mathfrak q^{\,q}$; and second, for every $\rho = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, the weight-$6$ slash action of $\rho^{\sharp} = \begin{pmatrix} a & b/q \\ qc & d \end{pmatrix}$ (the conjugate [`ModularCurve.FullLevel.conjElemN q ρ`](def/ModularCurve_FullLevelLevelAutAt.html#L13)) fixes $C_6$.
--
--   This supplies, at level $q$, a holomorphic weight-$6$ form on $\Gamma_{H_q}(q^2M')$ whose $q$-expansion is the Tate-curve invariant $c_6$ evaluated at parameter $\mathfrak q^{\,q}$, together with invariance under the $\Gamma_0(M')$-conjugates $\rho^{\sharp}$; a suitable multiple of $E_6$ stretched by $\mathrm{diag}(q,1)$ is the expected witness. It is used in the construction of forms whose $q$-expansions realise prescribed cusp data, via [`ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq`](thm.html#ModularCurve.FullLevel.Diamond.exists_modularForm_mul_qExpansion_eq_cuspPoint_and_slash_conjElemN_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_six_qExpansion_eq_cSix_tateBase
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ C6 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 6,
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C6)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₆ ∧
      ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C6 ∣[(6 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C6 := by sorry
