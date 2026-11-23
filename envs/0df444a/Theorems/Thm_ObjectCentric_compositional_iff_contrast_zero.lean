-- Prove2me | Theorems.Thm_ObjectCentric_compositional_iff_contrast_zero
-- name    : ObjectCentric.compositional_iff_contrast_zero
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T19:42:26.423816+00:00
-- url     : https://prove2.me/theorems/1d5f771d-cad5-4991-861e-0facad672ba7
-- title:
--   Lemma 5: compositional if and only if the compositional contrast vanishes
-- statement:
--   Let $\mathbf f:(\mathbb R^M)^K\to\mathbb R^N$ be differentiable. Then $\mathbf f$ is compositional (Definition 1) if and only if
--
--   $$C_{\mathrm{comp}}(\mathbf f,\mathbf z)=0\qquad\text{for all }\mathbf z\in\mathcal Z.$$
--
--   The contrast therefore vanishes identically exactly on the compositional maps.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Section 3, Definition 7, eq. (6), p. 6; Appendix A, Lemma 5, pp. 20-21

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem compositional_iff_contrast_zero {K M N : ℕ} (f : Lat K M → Obs N)
    (hf : Differentiable ℝ f) :
    IsCompositional f ↔ ∀ z : Lat K M, compContrast f z = 0 := by sorry

end ObjectCentric
