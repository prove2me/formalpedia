-- Prove2me | Theorems.Thm_OWMR_con_offset_exists
-- name    : OWMR.con_offset_exists
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:35.349479+00:00
-- url     : https://prove2.me/theorems/e9acec3f-f43f-424e-a658-81963ec1501a
-- title:
--   Lemma C.7: a rational offset with expected proxy within $2^{-j}$ of its average
-- statement:
--   Let $\nu$ be a probability measure, $K,\ hp\ge0$, $Q>0$, $0\le A_k\le Q$ an allocation path, and $X_b(k)\ge0$ measurable in $b$. For an offset $\vartheta$ let
--   $$z(\vartheta)=\int\Bigl[K\bigl(1+N(\vartheta)\bigr)+hp\sum_{k\le L}\bigl(A_k-S_k(\vartheta)-X_b(k)\bigr)^+\Bigr]\nu(db),$$
--   with $S_k(\vartheta)$ the shipped quantity of Lemma C.3 and $N(\vartheta)$ the number of interior thresholds. Let $e$ enumerate $\mathbb Q\cap(0,1)$. Then for every $j$ there is $k$ with $z(e_k)<\int_0^1z(\vartheta)\,d\vartheta+2^{-j}$. Hence the deterministic offset rule of Definition 2 (the first rational in the enumeration with this property) is well defined.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 7, Lemma C.7 and the credited proxy (C.29), p. E.20.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem con_offset_exists {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (K hp Q : ℝ) (hK : 0 ≤ K) (hhp : 0 ≤ hp) (hQ : 0 < Q) (A : ℕ → ℝ) (hA0 : ∀ k, 0 ≤ A k)
    (hAQ : ∀ k, A k ≤ Q) (L : ℕ) (X : β → ℕ → ℝ) (hXm : ∀ k, Measurable fun b => X b k)
    (hX0 : ∀ b k, 0 ≤ X b k) (e : ℕ ≃ {q : ℚ // 0 < q ∧ q < 1}) (j : ℕ) :
    ∃ k : ℕ, ∫⁻ b, ENNReal.ofReal (K * (1 + if ((e k : ℚ) : ℝ) < 1 / 3 then 2 else 1)
          + hp * ∑ k' ∈ Finset.range (L + 1),
            max (A k' - shippedPath Q ((e k : ℚ) : ℝ) A k' - X b k') 0) ∂ν
      < (∫⁻ θ in Set.Ioo (0 : ℝ) 1, ∫⁻ b, ENNReal.ofReal (K * (1 + if θ < 1 / 3 then 2 else 1)
          + hp * ∑ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0) ∂ν)
        + (2 : ℝ≥0∞)⁻¹ ^ j := by sorry
end OWMR
