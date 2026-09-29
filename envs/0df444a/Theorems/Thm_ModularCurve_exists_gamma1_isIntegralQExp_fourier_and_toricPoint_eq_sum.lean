-- Prove2me | Theorems.Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
-- name    : ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/6f072071-7c88-5a95-be88-e1ec0cd5b667
-- title:
--   Integral q-expansions of division-value forms and their toric values
-- statement:
--   Let $M$ be a positive integer. The assertion is the existence of two families of modular forms indexed by $\mathbb{Z}/M$, namely $B_c$ of weight $2$ and $D_c$ of weight $4$ for the congruence subgroup $\Gamma_1(M)$ viewed inside $\mathrm{GL}_2(\mathbb{R})$, together with power series $b_c, d_c \in \mathbb{Z}[[q]]$, such that: (i) for every $c$ the coefficientwise image of $b_c$ in $\mathbb{C}[[q]]$ is the $q$-expansion of $B_c$ of period $1$, and likewise $d_c$ for $D_c$; (ii) for every $c$ and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ one has $B_c \mid_2 \gamma = B_{c\,\gamma_{00}}$ and $D_c \mid_4 \gamma = D_{c\,\gamma_{00}}$, the index being multiplied by the reduction mod $M$ of the upper-left entry of $\gamma$; (iii) for every field $K$, every primitive $M$-th root of unity $\zeta \in K$ and every nonzero $s \in \mathbb{Z}/M$, writing $X$ for the first component of $\mathrm{toricPoint}\,K\,1\,(\zeta^{s.\mathrm{val}})$, i.e. the Laurent series over $K$ with constant term $u/(1-u)^2$ and $n$-th coefficient $\sum_{d \mid n} (n/d)\bigl(u^{n/d}+u^{-n/d}\bigr) - 2\sigma_1(n)$ at $u = \zeta^{s.\mathrm{val}}$, the two identities
--   $$M^3\,(1 + 12X) = \sum_{c \in \mathbb{Z}/M} \zeta^{(sc).\mathrm{val}} \cdot b_c, \qquad M^5\,\bigl(X + 6X^2 + 2a_4\bigr) = \sum_{c \in \mathbb{Z}/M} \zeta^{(sc).\mathrm{val}} \cdot d_c$$
--   hold in $K((q))$, where the $b_c, d_c$ are mapped into $K((q))$ coefficientwise and $a_4$ is the fourth coefficient of the Tate curve $\langle 1,0,0,a_4,a_6\rangle$ over $K((q))$ obtained from its integral model.
--
--   Classically these are the weight-two division values $12\,\wp(t/M;\tau)/(2\pi i)^2$ and the associated weight-four forms on $\Gamma_1(M)$, replaced here by their finite Fourier transforms over $\mathbb{Z}/M$ so as to have integral $q$-expansions and a $\Gamma_0(M)$-action permuting the index by the upper-left entry; clause (iii) identifies their values with the coordinates of the $M$-torsion toric points of the Tate curve over an arbitrary field containing a primitive $M$-th root of unity. It is used in the construction of elements of the $q$-expansion function field of the modular curve, through [`ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1`](thm.html#ModularCurve.c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1) and [`ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq`](thm.html#ModularCurve.exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

universe u in

theorem ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(B c) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type u) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 +
                6 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (ModularCurve.tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (d c) := by sorry
