-- Prove2me | Theorems.Thm_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
-- name    : ModularCurve.exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b7540678-d728-506d-b98e-3d892d309f5c
-- title:
--   Exponential decay of cusp-regular differentials pulled back to H
-- statement:
--   Fix $N \ge 1$ and write $\mathbb{C}F_N$ for the intermediate field [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) of $\mathbb{C}((q))$ over $\mathbb{C}$, namely the field generated over $\mathbb{C}$ by the coefficientwise images under $\mathbb{Q} \to \mathbb{C}$ of the elements of [`ModularCurve.modularFunctionFieldFull N`](def/ModularCurve_X0.html#L305). It is assumed that every place $w$ of $\mathbb{C}F_N/\mathbb{C}$ — a valuation subring of $\mathbb{C}F_N$, distinct from the whole field, containing $\mathbb{C}$ and a principal ideal ring — satisfies `DCoordGenerates`: the single element $D_{\mathbb{C}}(\pi_w)$, for $\pi_w$ the chosen uniformiser of $w$, spans the module of Kähler differentials $\Omega_{\mathbb{C}F_N/\mathbb{C}}$, so that for a differential $\eta$ one may write $\eta = f \cdot D_{\mathbb{C}}(\pi_w)$ and set $\operatorname{ord}_w(\eta) := \operatorname{ord}_w(f)$. Let $a, x \in \mathbb{C}F_N$ and assume that $\operatorname{ord}_v\bigl(a \cdot D_{\mathbb{C}}x\bigr) \ge 0$ holds for every place $v$ whose valuation subring does not contain the element $\hat\jmath \in \mathbb{C}F_N$ obtained from [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= q^{-1} \cdot \mathrm{jNumQ}(q)$ by the coefficient embedding. Let $\sigma \in SL(2,\mathbb{Z})$. Then there is $\delta > 0$ such that the weight-$2$ slash by $\sigma$ of the function $\tau \mapsto \widetilde a(\tau) \cdot \widetilde x'(\tau)$ on the upper half plane is $O\bigl(e^{-\delta \operatorname{Im}\tau}\bigr)$ as $\operatorname{Im}\tau \to \infty$; here $\widetilde y =$ [`ModularCurve.realize N y`](def/ModularCurve_ComplexPlaceDictionary.html#L17) sends $\tau$ to $g(\tau)/h(\tau)$ for some weight-$k$ modular forms $g, h$ on $\Gamma_0(N)$ with $h(\tau) \ne 0$ and $y \cdot q\text{-exp}(h) = q\text{-exp}(g)$ (and to $0$ if no such data exist), and $\widetilde x'$ is the complex derivative of $\widetilde x$ computed along `UpperHalfPlane.ofComplex`.
--
--   This is the analytic half of the dictionary between algebraic differentials on $X_0(N)_{\mathbb{C}}$ and weight-$2$ forms: regularity of $a\,dx$ at the places above $j = \infty$ is converted into vanishing of the constant term of the $q_h$-expansion of $(\widetilde a \widetilde x')\mid_2 \sigma$ at each cusp, expressed as exponential decay at $i\infty$. It is used in the construction of slash-invariant functions with prescribed nonvanishing residue at a point, via [`ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne`](thm.html#ModularCurve.ComplexPlaceDictionary.exists_slashInvariant_residue_ne_zero_of_pt_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
    (N : ℕ) [NeZero N]
    [∀ w : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      w.DCoordGenerates]
    (a x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))
    (hreg : ∀ v : AlgebraicCurve.Place ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      (⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
          ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
            (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩ :
          ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ∉
        v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ
        (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => ModularCurve.realize N (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by sorry
