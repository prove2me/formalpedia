-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_mass
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:07:43.449368+00:00
-- url     : https://prove2.me/theorems/cbf08df7-ef3b-4287-a4fb-2ab7d69be854
-- title:
--   Periodising a chirp-modulated cutoff preserves its $L^2$ mass
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$, let $\alpha<\tfrac12$ be such that the closed support of $g$ is contained in $[-\alpha,\alpha]$, and let $t$ be real. Let $\Gamma_{g,t}:\mathbb{R}/\mathbb{Z}\to\mathbb{C}$ be the periodised chirp, given by $\Gamma_{g,t}(x\bmod1)=g(x)\,e^{2\pi i\,tx^2/2}$ for $-\tfrac12<x\le\tfrac12$. Then, integrating over the circle with respect to its Haar probability measure,
--
--   $$
--   \int_{\mathbb{R}/\mathbb{Z}}|\Gamma_{g,t}(z)|^2\,dz=\int_{\mathbb{R}}|g(x)|^2\,dx .
--   $$
--
--   Periodising a chirp-modulated function whose support fits into one period is therefore an isometry for the $L^2$ norm: the chirp factor has modulus one and no overlaps occur. Combined with Parseval's identity on the circle and the identification of the Fourier coefficients of $\Gamma_{g,t}$ with the chirp integrals $\int g(x)e^{2\pi i(tx^2/2-wx)}\,dx$, it shows that the squared moduli of these integrals, summed over all $w\in\mathbb{Z}$, give $\int|g|^2$ for every curvature $t$.
--
--   **Formalization Note** $\Gamma_{g,t}$ is `circleChirp g t` and the measure on the circle is `AddCircle.haarAddCircle`. No regularity of $g$ is assumed; both sides are Bochner integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L445-L465

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

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass {g : ℝ → ℂ} {α : ℝ} (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    (∫ z : UnitAddCircle, ‖circleChirp g t z‖^2 ∂AddCircle.haarAddCircle) =
      ∫ x : ℝ, ‖g x‖^2 := by sorry
