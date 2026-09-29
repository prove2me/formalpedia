-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/1768f385-e19e-5d0b-bf74-45d0e6151ca4
-- title:
--   Weight-four form with q-expansion c₄ of Tate(q^q)
-- statement:
--   Let $q$ be a prime, let $M'$ be a nonzero natural number with $q \nmid M'$, let $L$ be a field of characteristic zero and let $\iota : L \to \mathbb{C}$ be a ring homomorphism. The assertion is the existence of a modular form $C_4$ of weight $4$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by [`CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/CohCarrier_Level.html#L133), that is, by the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(q^2M')$ whose lower-right entry, viewed in $(\mathbb{Z}/q^2M')^\times$, lies in the kernel of reduction to $(\mathbb{Z}/q)^\times$ (so $d \equiv 1 \bmod q$), such that two conditions hold. First, the $q$-expansion of $C_4$ at the cusp $\infty$ with period $1$, regarded as a Laurent series over $\mathbb{C}$, equals the coefficientwise image under $\iota$ of the invariant $c_4$ of the Weierstrass curve [`ModularCurve.tateBase L q`](def/ModularCurve_TateSlots.html#L46), namely the Tate curve over $\mathrm{LaurentSeries}\ L$ after the substitution multiplying all exponents by $q$. Second, for every $\rho \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$, the weight-$4$ slash action of [`ModularCurve.FullLevel.conjElemN q ρ`](def/ModularCurve_FullLevelLevelAutAt.html#L13), the element of $\mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ for $\rho = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, fixes $C_4$.
--
--   This produces, at level $q$, a weight-four form on the group $\Gamma_{H}(q^2M')$ whose $q$-expansion is the $c_4$-invariant of the Tate curve with parameter $\mathfrak q^{q}$ (a multiple of the Eisenstein series $E_4$ pulled back along $\tau \mapsto q\tau$), together with invariance under the $\Gamma_0(M')$-conjugates $\rho^{\sharp}$. It feeds the combined statement [`ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour`](thm.html#ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase.lean

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

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_four_qExpansion_eq_cFour_tateBase
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∃ C4 : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 4,
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑C4)) =
        ModularCurve.coeffMap ι (ModularCurve.tateBase L q).c₄ ∧
      ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
        (⇑C4 ∣[(4 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) = ⇑C4 := by sorry
