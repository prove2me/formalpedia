-- Prove2me | Theorems.Thm_LearnVsOpt_eq_14_15
-- name    : LearnVsOpt.eq_14_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:15.253318+00:00
-- url     : https://prove2.me/theorems/7d8d3dd0-c16b-4d63-acf9-8f860f460580
-- title:
--   (14)–(15), p.15 — $\|\delta(f,k)\|^2\le5$ and $\mathbb E_{k\sim f}[\delta(f,k)]=0$
-- statement:
--   Let $f$ be a forecast over a dictionary of distinct vectors in $[0,1]^{2n_L}$ in which the null action costs $0$, and let the response at $uc(f)$ be valid. The single-round joint error satisfies two properties.
--
--   1. **Bounded norm.** For every index $k$ of the dictionary,
--   $$
--   \|\delta(f,k)\|^2=\|\delta^R(f,k)\|_{L^2}^2+\|\delta^L(f,k)\|_2^2\le5 .
--   $$
--   2. **Unbiasedness under its own forecast.** If the realized index is drawn from $f$ itself,
--   $$
--   \mathbb E_{k\sim f}[\delta(f,k)]=0 ,
--   $$
--   in every coordinate.
--
--   These are the two facts that drive the potential argument for $\|Z_t\|^2$.
--
--   Differences from the source:
--   - encoding: f ∈ Δ_{n̂} → f : ℕ → ℝ with IsForecast (nonnegative, zero past the dictionary, sum 1); reason: the paper's own extension by zero, p.16
--   - generalization: f ∈ Δ_{n̂_O} over 𝒰𝒞 → f over any dictionary of distinct vectors in [0, 1]^{2n_L} with c[j₀] = 0; reason: 𝒰𝒞 is such a dictionary, and the paper uses the same bound over 𝒰𝒞_{t−1}
--   - generalization: any consistent tie-breaking rule, with J⃗ = (j, j) and Q = 0 for a pure best response (p.8) → every selector valid on (u, c) ∈ [0, 1]^{2n_L} with c[j₀] = 0; the only condition on J⃗ is j₁ = j₂ → Q = 0, so a pair j₁ ≠ j₂ with Q ∈ {0, 1} is also allowed; reason: the paper's rule is a valid selector, and its arguments use no more than validity
--   - encoding: δ(f, k), k an index of 𝒰𝒞 → δ(f, v), v = uc^(k) the realized vector; the indicator 1_{k=k'} reads D[k'] = v; reason: same object for a dictionary without repeats; also defined for a vector not yet observed
--   - encoding: E_{k∼f}[δ(f, k)] = 0 → Σ_k f_k · (coordinate of δ(f, k)) = 0 for each coordinate; reason: the expectation of a vector is taken coordinate by coordinate
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, (14)–(15), p.15

import Mathlib
import Definitions.Def_LearnVsOpt_Errors

namespace LearnVsOpt

/-- **Bounded norm and unbiasedness of the single-round error** (Fikioris, Sivan & Tardos,
arXiv:2611.05580, (14)–(15), p.15). For a forecast `f` over a dictionary `D` of distinct vectors in
`[0, 1]^{2n_L}` in which the null action has cost `0`, with `s` the valid response at `uc(f)`:
`‖δ(f, k)‖² ≤ 5` for every index `k` of `D`, and `E_{k∼f}[δ(f, k)] = 0`, coordinate by coordinate. -/
theorem eq_14_15 {nL : ℕ} (ρL : ℝ) (hρ₀ : 0 < ρL) (hρ₁ : ρL ≤ 1) (j₀ : Fin nL) (sel : Selector nL)
    (hsel : IsValidSel j₀ ρL sel) (D : List (UC nL)) (hnd : D.Nodup)
    (hD : ∀ e ∈ D, (∀ j, e.1 j ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ j, e.2 j ∈ Set.Icc (0 : ℝ) 1) ∧ e.2 j₀ = 0)
    (f : ℕ → ℝ) (hf : IsForecast D.length f) (s : Selection nL)
    (hs : s = (sel (ucOf D f).1 (ucOf D f).2).val) :
    (∀ k < D.length,
      JointVec.inner D.length (delta ρL D s f (D.getD k 0)) (delta ρL D s f (D.getD k 0)) ≤ 5) ∧
    (∀ k' j₁ j₂ q, ∑ k ∈ Finset.range D.length, f k * (delta ρL D s f (D.getD k 0)).R k' j₁ j₂ q = 0) ∧
    (∀ j, ∑ k ∈ Finset.range D.length, f k * (delta ρL D s f (D.getD k 0)).Lu j = 0) ∧
    (∀ j, ∑ k ∈ Finset.range D.length, f k * (delta ρL D s f (D.getD k 0)).Lc j = 0) ∧
    ∑ k ∈ Finset.range D.length, f k * (delta ρL D s f (D.getD k 0)).Luy = 0 ∧
    ∑ k ∈ Finset.range D.length, f k * (delta ρL D s f (D.getD k 0)).Lcy = 0 := by sorry

end LearnVsOpt
