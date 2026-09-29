-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero
-- name    : LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/36c6643e-130a-5c40-aba3-cd3c1ad39c31
-- title:
--   Integrality of torus parameters of an invariant Whittaker function
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}} = \mathbb{Z}$, with completion $\mathbb{Q}_v$ carrying its valuation $\mathrm{Valued.v}$ and valuation ring $\mathcal{O}_v$, and let $\psi_v : \mathbb{Q}_v \to \mathbb{C}^{\times}$ be an additive character. Assume $\psi_v$ is non-trivial somewhere on the set of $x$ with $\mathrm{Valued.v}(x) \le \exp(1)$, i.e. there is such an $x$ with $\psi_v(x) \neq 1$. Let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the Whittaker transformation law `IsGL3PsiWhittakerFn`: for all $x, y, z \in \mathbb{Q}_v$ and all $g$, $W(u(x,y,z)\,g) = \psi_v(x+y)\,W(g)$, where $u(x,y,z)$ is the upper unipotent matrix with rows $(1,x,z)$, $(0,1,y)$, $(0,0,1)$; assume further that $W$ is right invariant under the integral upper unipotent matrices, that is $W(g\,u(x,y,z)) = W(g)$ whenever $x, y, z \in \mathcal{O}_v$. Let $t_1, t_2 \in \mathbb{Q}_v^{\times}$ and suppose $W$ does not vanish at the image of $\mathrm{diag}(t_1,t_2)$ under the block embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$, $h \mapsto \mathrm{diag}(h,1)$. Then $t_1 t_2^{-1} \in \mathcal{O}_v$ and $t_2 \in \mathcal{O}_v$.
--
--   This is the elementary support condition for Whittaker functions on $\mathrm{GL}_3$ over a local field: an unramified-vector Whittaker function vanishes at torus points outside the dominant cone. It is used in the present development to constrain the torus support of local Whittaker functions, and is cited by the corresponding statement for torus points multiplied by a lower unipotent element in the $(2,1)$ position.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hinv : ∀ (g : LocalGL3 v) (x y z : v.adicCompletion ℚ),
      x ∈ v.adicCompletionIntegers ℚ → y ∈ v.adicCompletionIntegers ℚ → z ∈ v.adicCompletionIntegers ℚ →
        W (g * upperUnipotent3 x y z) = W g)
    (t₁ t₂ : (v.adicCompletion ℚ)ˣ) (hW0 : W (iotaGL (diagUnits2 t₁ t₂)) ≠ 0) :
    (t₁ : v.adicCompletion ℚ) * (t₂ : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ ∧
      (t₂ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by sorry
