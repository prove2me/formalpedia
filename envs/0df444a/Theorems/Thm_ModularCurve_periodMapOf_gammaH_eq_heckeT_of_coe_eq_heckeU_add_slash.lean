-- Prove2me | Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
-- name    : ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3916f231-07a7-51b0-ab63-62483f880d0a
-- title:
--   Period map intertwines classical T_ℓ with cohomological T_ℓ
-- statement:
--   Fix $M \ge 1$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma_H(M)$ denote the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the set of $\gamma \in \Gamma_0(M)$ whose unit $\bar d_\gamma \in (\mathbb{Z}/M)^\times$, the reduction of the $(1,1)$ entry (with inverse the reduction of the $(0,0)$ entry), lies in $H$. Let $\ell$ be a prime with $\ell \nmid M$, and let $\rho \in \Gamma_0(M)$ be an element whose $(1,1)$ entry reduces to $\ell$ in $\mathbb{Z}/M$. Let $f, g$ be weight-$2$ cusp forms for $\Gamma_H(M)$ such that, as functions on the upper half-plane, $g = \sum_{j=0}^{\ell-1} f \mid_2 \begin{pmatrix} 1 & j \\ 0 & \ell\end{pmatrix} + f \mid_2 \bigl(\rho \cdot \begin{pmatrix} \ell & 0 \\ 0 & 1\end{pmatrix}\bigr)$, where $\rho$ is viewed in $\mathrm{GL}_2(\mathbb{R})$ and the first sum is [`ModularForm.heckeU 2 ℓ`](def/ModularForm_HeckeOperator.html#L93). The conclusion is an identity in $H^1$-characters of $\Gamma_H(M)$ with values in $\mathbb{C}$: the period homomorphism [`ModularCurve.periodMapOf`](def/ModularCurve_PeriodOf.html#L79) of $g$ equals [`CohCarrier.heckeT M H ℓ ℂ`](def/CohCarrier_Level.html#L250) applied to the period homomorphism of $f$; here `periodMapOf h` is the period character attached to a choice of equivariant primitive of $h$ vanishing at $i\infty$ with limits along all $\mathrm{SL}_2(\mathbb{Z})$-translates (and $0$ if none exists), while `heckeT` sends a character $\varphi$ to the transfer from the subgroup `GammaHUpper M H ℓ` of the character $\varphi$ precomposed with the conjugation map [`CohCarrier.conjL M H ℓ`](def/CohCarrier_Level.html#L228) into $\Gamma_H(M)$.
--
--   This is the Hecke equivariance of the Eichler–Shimura period map for the groups $\Gamma_H(M)$ between $\Gamma_1(M)$ and $\Gamma_0(M)$: the right-hand side is the representative-free, transfer-theoretic $T_\ell$ on group cohomology, while the hypothesis on $g$ expresses the classical double-coset operator $U_\ell + \langle \ell\rangle \mid_2 \mathrm{diag}(\ell,1)$ on weight-$2$ cusp forms. It is used in the construction of the Eichler–Shimura map into $H^1(\Gamma_H(M), \mathbb{C})$ and in extracting Hecke eigenforms with prescribed $q$-expansion coefficients from eigenvectors in cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (ρ : CongruenceSubgroup.Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 ℓ ⇑f +
      (⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ))) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by sorry
