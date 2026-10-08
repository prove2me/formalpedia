-- Prove2me | Theorems.Thm_KLTNuclear_Oracle_eq_2_9
-- name    : KLTNuclear.Oracle.eq_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:48.434574+00:00
-- url     : https://prove2.me/theorems/a91c7e62-7aae-4a14-bd55-b18ba9a55418
-- title:
--   (2.9) — polarization identity for the $L_2(\Pi)$ inner product
-- statement:
--   For a sample with square-integrable design entries and any $m_1\times m_2$ matrices $B$, $A$, $A_0$,
--   $$2\langle B-A_0,B-A\rangle_{L_2(\Pi)}=\|B-A_0\|^2_{L_2(\Pi)}+\|B-A\|^2_{L_2(\Pi)}-\|A-A_0\|^2_{L_2(\Pi)}.$$
--
--   In the proof of Theorem 1 it is applied with $B=\hat A^\lambda$ to turn the cross term of (2.8) into the three squared distances of (2.11).
--
--   **Formalization Note** The paper states it with $B=\hat A^\lambda$; the identity holds for every $B$ and is stated so. Square integrability of the design entries is what makes $\langle\cdot,\cdot\rangle_{L_2(\Pi)}$ bilinear.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 8, (2.9)

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model

open MeasureTheory MatrixCompletion

namespace KLTNuclear.Oracle

/-- (2.9) (p. 8): polarization identity for the L₂(Π) inner product, stated for arbitrary
matrices B (in the paper B = Â^λ), A and A₀. -/
theorem eq_2_9 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (B A A₀ : RealMatrix m₁ m₂) :
    2 * l2Inner P X (B - A₀) (B - A) =
      l2NormSq P X (B - A₀) + l2NormSq P X (B - A) - l2NormSq P X (A - A₀) := by sorry

end KLTNuclear.Oracle
