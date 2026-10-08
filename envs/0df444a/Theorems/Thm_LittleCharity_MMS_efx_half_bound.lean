-- Prove2me | Theorems.Thm_LittleCharity_MMS_efx_half_bound
-- name    : LittleCharity.MMS.efx_half_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:29:55.464023+00:00
-- url     : https://prove2.me/theorems/f4d2624c-2af8-43df-acee-fea357f248d3
-- title:
--   Proof of Theorem 14, p. 15 — under EFX, v_i(X_i) ≥ (1 − 1/|X_j|)·v_i(X_j) ≥ ½·v_i(X_j) whenever |X_j| ≥ 2
-- statement:
--   Let the valuations be additive and let $X$ be EFX. For agents $i,j$ with $|X_j|\ge 2$,
--   $$v_i(X_i)\ \ge\ \Bigl(1-\frac{1}{|X_j|}\Bigr)\, v_i(X_j)\ \ge\ \frac12\, v_i(X_j).$$
--
--   This is the step of the proof of Theorem 14 that turns the EFX property into inequality (3): an agent never values another agent's bundle of at least two goods at more than twice her own bundle.
--
--   **Formalization Note** The conclusion is the conjunction of the two inequalities $(1-1/|X_j|)v_i(X_j)\le v_i(X_i)$ and $\tfrac12 v_i(X_j)\le v_i(X_i)$, with $|X_j|$ cast to $\mathbb{R}$. The page states it for $j\in N'$; the statement holds for every pair $i,j$ and is posed so.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 15, proof of Theorem 14, second paragraph and its display

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.MMS

/-- Proof of Theorem 14, p. 15: under EFX and additivity, if `|X_j| ≥ 2` then
`v_i(X_i) ≥ (1 − 1/|X_j|)·v_i(X_j) ≥ ½·v_i(X_j)`. -/
theorem efx_half_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) :
    (1 - 1 / ((X j).card : ℝ)) * v i (X j) ≤ v i (X i) ∧
      (1 / 2 : ℝ) * v i (X j) ≤ v i (X i) := by sorry

end LittleCharity.MMS
