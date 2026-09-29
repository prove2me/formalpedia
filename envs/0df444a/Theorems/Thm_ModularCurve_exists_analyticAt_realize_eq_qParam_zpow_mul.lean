-- Prove2me | Theorems.Thm_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul
-- name    : ModularCurve.exists_analyticAt_realize_eq_qParam_zpow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/60501806-7bc5-5f0b-91ea-cee9e87a4b8e
-- title:
--   q-chart at the cusp: xᵃⁿ=q^{ord}· G(q)
-- statement:
--   Fix a positive integer $N$ and let $\mathbb{C}F_N =$ [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) be the subfield of the formal Laurent series field $\mathbb{C}(\!(q)\!)$ obtained by adjoining to $\mathbb{C}$ the image, under the coefficientwise extension of $\mathbb{Q}\hookrightarrow\mathbb{C}$, of the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}\,\mathbb{Q}\,d\,jq$ for the nonzero divisors $d \mid N$. Let $x \in \mathbb{C}F_N$ with $x \neq 0$, and write again $x$ for the underlying Laurent series, with order $e = \operatorname{ord}(x) \in \mathbb{Z}$. Then there is a function $G : \mathbb{C} \to \mathbb{C}$, analytic at $0$, such that $G(0)$ is the coefficient of $x$ in degree $e$ (its leading coefficient), and such that, for $\tau$ in the upper half-plane with $\operatorname{Im}\tau$ sufficiently large (eventually along the filter `atImInfty`),
--   $$\mathrm{realize}\,N\,x\,(\tau) = q(\tau)^{e}\, G\bigl(q(\tau)\bigr), \qquad q(\tau) = e^{2\pi i \tau},$$
--   where $\mathrm{realize}\,N\,x$ is the function on $\mathbb{H}$ defined, whenever there exist an integer $k$ and modular forms $g,h$ of weight $k$ on $\Gamma_0(N)$ with $h(\tau) \neq 0$ and $x \cdot \widetilde{h} = \widetilde{g}$ as Laurent series (tildes denoting the $q$-expansions of width $1$), as $g(\tau)/h(\tau)$ for such a chosen pair, and as $0$ otherwise.
--
--   This is the statement that $q = e^{2\pi i\tau}$ is a local parameter at the cusp $i\infty$ of $X_0(N)(\mathbb{C})$, and that the formal $q$-expansion of an element of the modular function field is, to leading order, the genuine Laurent expansion of its realization on the upper half-plane in that chart. It is used in the construction of sequences of points approaching the cusp along which places of the function field are evaluated, in [`ModularCurve.exists_seq_place_tendsto_evalAt`](thm.html#ModularCurve.exists_seq_place_tendsto_evalAt) and [`ModularCurve.exists_seq_place_tendsto_evalAt_cuspInftyBar`](thm.html#ModularCurve.exists_seq_place_tendsto_evalAt_cuspInftyBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped Topology

theorem ModularCurve.exists_analyticAt_realize_eq_qParam_zpow_mul (N : ℕ) [NeZero N]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (hx : x ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      G 0 = (x : LaurentSeries ℂ).coeff (x : LaurentSeries ℂ).order ∧
      ∀ᶠ τ in atImInfty, ModularCurve.realize N (x : LaurentSeries ℂ) τ =
        Function.Periodic.qParam 1 (τ : ℂ) ^ (x : LaurentSeries ℂ).order *
          G (Function.Periodic.qParam 1 (τ : ℂ)) := by sorry
