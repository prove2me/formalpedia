-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_cand_card_le
-- name    : OptInapprox.MaxCut.cand_card_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:57.923539+00:00
-- url     : https://prove2.me/theorems/6170290b-07c3-4ca1-901e-538db982408f
-- title:
--   §8.3, pp. 19–20 — Σ_i Inf_i^{≤k}(f) ≤ k, hence |Cand| ≤ 2k/δ
-- statement:
--   Let $f:\{-1,1\}^n\to[-1,1]$, $k\in\mathbb N$ and $\delta>0$. Then
--   $$\sum_{i}\mathrm{Inf}_i^{\le k}(f)\le k,$$
--   and hence the set of candidate coordinates $\mathrm{Cand}=\{i:\mathrm{Inf}_i^{\le k}(f)\ge\delta/2\}$ has $|\mathrm{Cand}|\le 2k/\delta$.
--
--   In the soundness proof each right vertex $w$ is labeled by a random element of $\mathrm{Cand}[w]$; this bound controls the loss.
--
--   **Formalization Note.** The paper applies this to the boolean-valued supposed Long Codes $f_w$; it is stated for every $[-1,1]$-valued $f$, which includes them.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 19–20, §8.3 Soundness (candidate sets Cand[w])

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.MaxCut

theorem cand_card_le {n : ℕ} (f : (Fin n → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1) (k : ℕ) (δ : ℝ)
    (hδ : 0 < δ) :
    ∑ i, lowDegInf k i f ≤ k ∧
      ((Finset.univ.filter fun i => δ / 2 ≤ lowDegInf k i f).card : ℝ) ≤ 2 * k / δ := by sorry

end OptInapprox.MaxCut
