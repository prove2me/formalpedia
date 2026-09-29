-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
-- name    : ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5a034f75-3040-5143-94ae-b5cbc6d22063
-- title:
--   Weight-two cusp forms with algebraic coefficients as differentials
-- statement:
--   Fix $M \ge 1$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbf Z)$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, a ring embedding $\iota_0 \colon \overline{\mathbf Q} \to \mathbf C$ (for Mathlib's algebraic closure of $\mathbf Q$), and a cusp form $f$ of weight $2$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbf R)$, and assume that for every $n$ the $n$-th coefficient of the $q$-expansion of $f$ (with respect to the period $1$) lies in the image of $\iota_0$. Let $F =$ `qExpFunctionFieldC ℚ Γ` be the subfield of $\mathbf Q((q))$ generated over $\mathbf Q$ by the quotients $p_f/p_g$ of the Laurent series attached to integral $q$-expansions $p_f, p_g \in \mathbf Z[[q]]$ of modular forms $f, g$ of a common weight $k$ on $\Gamma$, with $p_g \neq 0$ in $\mathbf Q((q))$, and let $\bar F$ be its base change, i.e. the subfield of $\overline{\mathbf Q}((q))$ generated over $\overline{\mathbf Q}$ by the coefficientwise image of $F$. The assertion is that there exists a Kähler differential $\omega \in \Omega_{\bar F/\overline{\mathbf Q}}$ such that applying `qExpansionDiffAlong` for the inclusion $\bar F \hookrightarrow \overline{\mathbf Q}((q))$ to $\omega$ — that is, the $\overline{\mathbf Q}$-linear map $\varphi$ on $\Omega_{\bar F/\overline{\mathbf Q}}$ characterised by $\varphi(\mathrm d x) = \mathtt{thetaL}(x)$ and $\varphi(x\,\omega) = x\,\varphi(\omega)$, chosen if such a map exists and $0$ otherwise — and pushing the resulting Laurent series coefficientwise along $\iota_0$ gives exactly the $q$-expansion of $f$, regarded as an element of $\mathbf C((q))$.
--
--   This is the arithmetic comparison between weight-two cusp forms with algebraic Fourier coefficients and Kähler differentials on the modular curve for $\Gamma$, realised at the level of $q$-expansions over $\overline{\mathbf Q}$; the subgroups allowed are exactly those of the form $\Gamma_H(M)$. It is used in the corresponding statement for the function field of $X_1$, on the way to attaching differentials, and hence Galois representations, to the cusp forms occurring in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve
open ModularCurve

theorem ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (ι₀ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n ∈ ι₀.range) :
    ∃ ω : Ω[↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.qExpansionDiffAlong (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)).val ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)) := by sorry
