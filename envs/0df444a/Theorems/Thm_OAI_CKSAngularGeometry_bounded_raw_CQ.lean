-- Prove2me | Theorems.Thm_OAI_CKSAngularGeometry_bounded_raw_CQ
-- name    : OAI.CKSAngularGeometry.bounded_raw_CQ
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:39:23.811307+00:00
-- url     : https://prove2.me/theorems/66c24fec-f993-4379-a7ba-7cbd3bf999f4
-- title:
--   Constraint estimates for bounded raw null inputs
-- statement:
--   Let $K$ be a compact set of $2\times 2$ scalar jet matrices with invertible values, and let $B\in\mathbb R$, $A\ge 0$. There are $R_0\ge 1$ and $C,D\ge 0$ such that for every raw null input $p$ with metric jet in $K$ and $\|p\|\le B$, and $r\ge R_0$ with $z(p)=1/r$, weight $w=$ `rwgt` $\ge 0$ and $|p_i|\le Aw$ for $i\ne 0$, writing $Q,Q_0$ for `coordinateQ` of the deformed and original input, $Z,Z_0$ for `coordinateZ`, and $E,E_0$ for the corresponding coordinate energies:
--   $$|Q_0|\le \frac{D}{r^3},\quad \Big|Q-Q_0-\frac{2w}{r^2}\Big|\le\frac{Cw}{r^3},\quad \Big|E-E_0-(Q-Q_0)-\frac{2w}{r^{3}\sqrt r}\Big|\le\frac{Cw}{r^4},$$
--   $$|Z_0^a|\le\frac{D}{r^2},\qquad |Z^a-Z_0^a|\le\frac{Cw}{r^2}.$$
--   The added quantity is controlled by the weight $w$ itself, so the estimate keeps its force where the activation weight is small.
--
--   **Formal statement.** In the scope of the preamble:
--
--   ```lean
--   theorem bounded_raw_CQ {K : Set MatrixScalarJet} (hK : IsCompact K)
--       (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B A : ℝ) (hA : 0 ≤ A) :
--       ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
--         ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
--         ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
--         (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
--         |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
--         |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
--           2*rwgt p.1/r^2| ≤ C*rwgt p.1/r^3 ∧
--         |(coordinateEnergy (rawNullMap p) r-coordinateEnergy (rawNullMap (rawNullOriginal p)) r)-
--             (coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1)))-
--           2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*rwgt p.1/r^4 ∧
--         (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
--         (∀ a, |coordinateZ (rawMomentumInput p.1) a-
--           coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*rwgt p.1/r^2)
--   ```
--
--   **Formalization Note** The statement is verbatim from `lean/OAI/Geometry/Relativity/CKS/CollarConstraintBounded.lean`, lines 16-60, in OpenAI's `openai/math` at commit `adc7f12` (Apache-2.0), formalizing part of the construction in the preprint *Area-controlled end replacement and the Bondi–Penrose inequality in the CKS class* (OpenAI, September 27, 2026). It is a supporting lemma for `OAI.CKSSourceExterior.area_controlled_end_replacement`. The definitions it mentions are those of `Definitions.Def_CKSBondiPenrose` and `Definitions.Def_CKSEndReplacementSupport`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Relativity/CKS/CollarConstraintBounded.lean#L16-L60 ; preprint preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf in the same repository

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_raw_CQ {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B A : ℝ) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        2*rwgt p.1/r^2| ≤ C*rwgt p.1/r^3 ∧
      |(coordinateEnergy (rawNullMap p) r-coordinateEnergy (rawNullMap (rawNullOriginal p)) r)-
          (coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1)))-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*rwgt p.1/r^4 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p.1) a-
        coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*rwgt p.1/r^2) := by
  sorry

end
end CKSAngularGeometry
end
end OAI
