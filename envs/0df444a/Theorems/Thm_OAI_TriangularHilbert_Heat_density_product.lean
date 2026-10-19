-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_density_product
-- name    : OAI.TriangularHilbert.Heat.density_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:35:30.324513+00:00
-- url     : https://prove2.me/theorems/2923e1da-4ac7-4f0c-8a9b-0b1e139d73c9
-- title:
--   Product formula for Gaussian densities
-- statement:
--   Let $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$. For $s,t>0$ and $a,b,p\in\mathbb R$,
--   $$
--   \phi_s(a-p)\,\phi_t(b-p)=\phi_{s+t}(a-b)\;\phi_{\frac{st}{s+t}}\Bigl(p-\frac{ta+sb}{s+t}\Bigr).
--   $$
--
--   A product of two Gaussians in the same variable is a Gaussian in that variable times a Gaussian in the difference of the centres. Integrating in $p$ gives the convolution identity $\phi_s*\phi_t=\phi_{s+t}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GaussianConvolution.lean#L23-L40

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory

theorem OAI.TriangularHilbert.Heat.density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b p : ℝ) :
    density s (a-p)*density t (b-p) =
      density (s+t) (a-b)*density (s*t/(s+t)) (p-(t*a+s*b)/(s+t)) := by sorry
