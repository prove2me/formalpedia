-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_fourier_truncation_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:06:31.380969+00:00
-- url     : https://prove2.me/theorems/9dae456d-c4d5-43c3-a919-6635f939394f
-- title:
--   Uniform error of a finite Fourier truncation under a summable majorant for the discarded coefficients
-- statement:
--   Let $f:\mathbb{R}/\mathbb{Z}\to\mathbb{C}$ be continuous, with Fourier coefficients $\widehat f(w)=\int_{\mathbb{R}/\mathbb{Z}}f(z)\,e^{-2\pi i wz}\,dz$ taken with respect to the Haar probability measure, and write $e_w(z)=e^{2\pi i wz}$ for $w\in\mathbb{Z}$. Let $S\subset\mathbb{Z}$ be a finite set and let $b:\mathbb{Z}\to\mathbb{R}$ be a summable family with $b(w)\ge0$ for all $w$, such that $|\widehat f(w)|\le b(w)$ for every $w\notin S$. Then for every $z\in\mathbb{R}/\mathbb{Z}$,
--
--   $$
--   \Bigl|\sum_{w\in S}\widehat f(w)\,e_w(z)-f(z)\Bigr|\le\sum_{w\in\mathbb{Z}}b(w).
--   $$
--
--   This is a sup-norm bound for the error of truncating a Fourier series to a finite set of frequencies, in terms of a summable majorant for the discarded coefficients; for simplicity the right-hand side sums $b$ over all of $\mathbb{Z}$, including $S$. In the chirp setting the majorant is a constant times $T^{-1}(1+|w|)^{-2}$, which produces truncation errors of order $1/T$ uniformly on the circle.
--
--   **Formalization Note** The function is a bundled continuous map (`ContinuousMap`) from `UnitAddCircle` to the complex numbers, $e_w$ is Mathlib's `fourier w`, and the coefficients are `fourierCoeff f w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L384-L414

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

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error (f : C(UnitAddCircle,ℂ)) (S : Finset ℤ)
    (b : ℤ → ℝ) (hb : Summable b) (hb0 : ∀ w, 0≤b w)
    (hbound : ∀ w, w ∉ S → ‖fourierCoeff f w‖ ≤ b w) (z : UnitAddCircle) :
    ‖(∑ w ∈ S, fourierCoeff f w*fourier w z)-f z‖ ≤ ∑' w, b w := by sorry
