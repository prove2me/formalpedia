-- Prove2me | Theorems.Thm_IntMul_HvdH_tensor_error
-- name    : IntMul.HvdH.tensor_error
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T23:03:41.836776+00:00
-- url     : https://prove2.me/theorems/0670b2f4-539b-49be-9997-b7713385996d
-- title:
--   Error of slice-wise tensor product approximations (Lemma 2.11)
-- statement:
--   Let $d\ge0$. For each axis $i$ let $A_i$ be a one-dimensional map that is nonexpansive for the max-norm (as is any linear map of norm $\le1$). Let $\tilde A_i$ map the closed unit ball into itself and approximate $A_i$ there with error at most $e_i$ in every entry. Then for every array $x$ in the unit ball, the slice-wise tensor products (see `IntMul_HvdH_SliceTensor`) satisfy
--   $$\Bigl\|\Bigl(\bigotimes_i\tilde A_i\Bigr)x-\Bigl(\bigotimes_iA_i\Bigr)x\Bigr\|_\infty\le\sum_ie_i.$$
--   This is the error statement $\varepsilon(\tilde A)\le\sum_i\varepsilon(\tilde A_i)$ of Lemma 2.11 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.7, Lemma 2.11 (tensor products)

import Definitions.Def_IntMul_HvdH_SliceTensor

namespace IntMul.HvdH
theorem tensor_error {d : ℕ} (A Aa : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (e : Fin d → ℝ)
    (hA : ∀ i, ∀ (x y : ℕ → ℂ) (δ : ℝ), (∀ k, ‖x k - y k‖ ≤ δ) → ∀ j, ‖A i x j - A i y j‖ ≤ δ)
    (hAa : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j‖ ≤ 1)
    (herr : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j - A i x j‖ ≤ e i)
    (x : (Fin d → ℕ) → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (j : Fin d → ℕ) :
    ‖tensorMap Aa x j - tensorMap A x j‖ ≤ ∑ i, e i := by sorry
end IntMul.HvdH
