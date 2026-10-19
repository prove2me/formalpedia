-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Spreading_quadratic_norm_scaled
-- name    : OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:10:12.96291+00:00
-- url     : https://prove2.me/theorems/30ab1a5f-360d-4475-95ab-19c509343979
-- title:
--   Uniform stationary-phase bound $T|\beta|\,\bigl|\int g(x)e^{2\pi i(T\beta x^2/2-ux)}dx\bigr|^2\le(1+C/T)^2$
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be infinitely differentiable with compact support and $|g(x)|\le1$ for all $x$, and let $\beta\ne0$ be real. Then there is a constant $C\ge0$ such that for every real $T>0$ and every real $u$,
--
--   $$
--   T|\beta|\cdot\Bigl|\int_{\mathbb{R}} g(x)\,e^{2\pi i\,(T\beta x^2/2-ux)}\,dx\Bigr|^2\le\Bigl(1+\frac{C}{T}\Bigr)^2 .
--   $$
--
--   Equivalently, the chirp integral with curvature $T\beta$ has modulus at most $(1+C/T)/\sqrt{T|\beta|}$, uniformly in the linear frequency $u$: this is the size predicted by stationary phase at the stationary point $x_0=u/(T\beta)$, with a relative error $O(1/T)$. In the Fourier-spreading construction the integrals with $u=w\in\mathbb{Z}$ are the Fourier coefficients of a periodised chirp; the bound says that each of them carries squared mass at most about $1/(T|\beta|)$, which complements the count of about $T|\beta|$ retained frequencies. The constant depends only on $g$ and $\beta$.
--
--   **Formalization Note** The integrand is `g x * phase (T*β) u x`, where `phase t u x` is $e^{2\pi i(tx^2/2-ux)}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Spreading.lean#L13-L42

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Spreading
universe uI uE uJ uK
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

theorem OAI.AsymptoticallyMinimalLittlewood.Spreading.quadratic_norm_scaled {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1)
    {β : ℝ} (hβ : β≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 0<T → ∀ u : ℝ,
      T*|β| *‖∫ x : ℝ, g x*phase (T*β) u x‖^2 ≤ (1+C/T)^2 := by sorry
