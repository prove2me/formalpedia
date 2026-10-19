-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_row_mass_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:08:11.781506+00:00
-- url     : https://prove2.me/theorems/cf8d403e-9ee1-4c46-a106-707e311f744f
-- title:
--   The window $|w|\le T|\beta|/2$ captures all but $O(1/T)$ of the squared Fourier mass of a chirp
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be infinitely differentiable with compact support and $|g(x)|\le1$ for all $x$, let $0\le\alpha<\tfrac12$ be such that the closed support of $g$ is contained in $[-\alpha,\alpha]$, and let $\beta\ne0$ be real. Then there is a constant $C\ge0$ such that for every real $T\ge1$,
--
--   $$
--   \int_{\mathbb{R}}|g(x)|^2\,dx-\frac{C}{T}\ \le\sum_{w\in\mathbb{Z},\ |w|\le T|\beta|/2}\ \Bigl|\int_{\mathbb{R}} g(x)\,e^{2\pi i\,(T\beta x^2/2-wx)}\,dx\Bigr|^2 .
--   $$
--
--   The integrals on the right are the Fourier coefficients of the periodised chirp $g(x)e^{\pi i T\beta x^2}$ on $\mathbb{R}/\mathbb{Z}$, and by Parseval's identity the sum of their squared moduli over all $w\in\mathbb{Z}$ equals $\int|g|^2$. The theorem says that the frequency window $|w|\le T|\beta|/2$ already captures this squared mass up to an error $O(1/T)$, with a constant depending on $g,\alpha,\beta$ but not on $T$. This is the scalar Parseval ingredient of the Fourier-spreading construction, which needs the retained coefficients to carry almost all of the energy.
--
--   **Formalization Note** The summation range is `box T β`, the integer interval from $-\lfloor T|\beta|/2\rfloor$ to $\lfloor T|\beta|/2\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L492-L538

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
universe uI uZ
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.row_mass_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      (∫ x : ℝ, ‖g x‖^2) - C/T ≤
        ∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2 := by sorry
