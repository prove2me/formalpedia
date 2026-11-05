-- Prove2me | Theorems.Thm_OAI_CKSAngularGeometry_bounded_thin_field_map_DEC
-- name    : OAI.CKSAngularGeometry.bounded_thin_field_map_DEC
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:58.70951+00:00
-- url     : https://prove2.me/theorems/1dd71474-6215-4915-bd6a-99ff3f3dcf09
-- title:
--   Uniform DEC transfer for thin collar fields
-- statement:
--   Fix a compact set $K$ of $2\times 2$ matrix jets whose value matrices $q$ satisfy $q_{11}>0$ and $\det q>0$, and constants $B,A\ge 0$. The theorem produces a radius $R_0\ge 1$ with the following property. Let $b\in\mathbb R^5$ be a parameter vector with $\|b\|\le B$, let $f$ be collar coefficient fields satisfying the thin bounds `ThinBoundedAt B` at a point $x$, with the jet of the angular metric at $x$ in $K$, and let $r\ge R_0$ with $b_0=1/r$, $b_4\ge 0$ and $|b_i|\le A\,b_4$ for $i\ne 0$. If the angular matrices of the deformed and original raw inputs are symmetric, then the coordinate dominant energy inequality for the original input implies it for the deformed input:
--   $$\texttt{coordinateDEC}(\texttt{rawNullMap}(\texttt{rawNullOriginal}(\texttt{fieldRaw}\ b\ f\ x)),r)\ \Longrightarrow\ \texttt{coordinateDEC}(\texttt{rawNullMap}(\texttt{fieldRaw}\ b\ f\ x),r).$$
--   The parameters in $b$ other than $b_0$ are controlled by the single activation weight $b_4$. This is the field-level form of the collar estimate that keeps DEC when the leaves are made round.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem bounded_thin_field_map_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
--         matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
--         ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
--         (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
--         (rawAngularMatrix (fieldRaw b f x)) 1 0=(rawAngularMatrix (fieldRaw b f x)) 0 1 →
--         (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 1 0=
--           (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 0 1 →
--         coordinateDEC (rawNullMap (rawNullOriginal (fieldRaw b f x))) r →
--         coordinateDEC (rawNullMap (fieldRaw b f x)) r
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/CollarThinInputs.lean`, lines 64-82, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/CollarThinInputs.lean#L64-L82 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_thin_field_map_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (rawAngularMatrix (fieldRaw b f x)) 1 0=(rawAngularMatrix (fieldRaw b f x)) 0 1 →
      (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 1 0=
        (rawAngularMatrix (rawNullOriginal (fieldRaw b f x))) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal (fieldRaw b f x))) r →
      coordinateDEC (rawNullMap (fieldRaw b f x)) r := by
  sorry

end
end CKSAngularGeometry
end
end OAI
