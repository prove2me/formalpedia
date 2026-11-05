-- Prove2me | Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
-- name    : OAI.CKSInducedSphere.smoothDatum_rapid
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:10.721243+00:00
-- url     : https://prove2.me/theorems/6eac41af-e3a1-401a-9b6b-f4810927a143
-- title:
--   Rapid decay of the heat polynomials of a smooth function on the sphere
-- statement:
--   For a smooth function $f$ on $S^2$, the sequence of harmonic coefficient polynomials `heatPolynomials f` (polynomial representatives of the $L^2$ harmonic projections of $f$ with index $n+2$) satisfies `PolynomialRapid`: for every word $w$ in the rotation fields and every $b\in\mathbb N$, the series
--   $$\sum_n \lambda_n^{\,b}\,\big\|\mathrm{rot}_w(p_n)|_{S^2}\big\|$$
--   converges, where $\lambda_n$ is the sphere Laplacian eigenvalue. This is the input for term-by-term differentiation of the heat series.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem smoothDatum_rapid (f : C(Sphere,ℝ)) (hf : SmoothSphere f) :
--       PolynomialRapid (heatPolynomials f)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/FullSphereHeat.lean`, lines 34-37, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/FullSphereHeat.lean#L34-L37 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

theorem smoothDatum_rapid (f : C(Sphere,ℝ)) (hf : SmoothSphere f) :
    PolynomialRapid (heatPolynomials f) := by
  sorry

end
end CKSInducedSphere
end
end OAI
