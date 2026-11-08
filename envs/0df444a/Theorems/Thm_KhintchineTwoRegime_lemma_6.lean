-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_6
-- name    : KhintchineTwoRegime.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:21.442646+00:00
-- url     : https://prove2.me/theorems/e7bd207d-5720-40ba-8487-3364fbe95aaa
-- title:
--   Lemma 6 — localization: $K_n(\omega)\le A(q)$ forces $0\le x<1/12$
-- statement:
--   Let $n\ge6$ and let $\omega\in\mathbb R^n$ be a proper unit vector with
--   $$
--   \frac{\sqrt{483}}{22}\le q=\omega_1+\omega_2<1,
--   $$
--   and put $A(q)=\dfrac{3q}4+\dfrac3{8\sqrt2}\sqrt{1-q^2}$ and $x=q-\omega_3-\omega_4$. If $K_n(\omega)\le A(q)$, then
--   $$
--   0\le x<\frac1{12}.
--   $$
--   Any competitor that could beat the six-coordinate profile must therefore have its first four coordinates nearly equal; this is the localization step in the proof of Theorem 2.
--
--   Differences from the source:
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 6, p.7

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_Abound

namespace KhintchineTwoRegime

/-- Lemma 6 (Localization of competing vectors) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.7): let `n ≥ 6` and let `ω ∈ ℝⁿ` be
a proper unit vector with `√483/22 ≤ q = ω₁ + ω₂ < 1`; put
`A(q) = 3q/4 + (3/(8√2))√(1 − q²)` and `x = q − ω₃ − ω₄`. If `K_n(ω) ≤ A(q)`, then
`0 ≤ x < 1/12`.

**Formalization Note** 0-based indices: `ω₁, …, ω₄` are `ω 0, …, ω 3`. -/
theorem lemma_6 (n : ℕ) (hn : 6 ≤ n) (ω : Fin n → ℝ) (hω : IsProper ω)
    (hq₁ : Real.sqrt 483 / 22 ≤ ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩)
    (hq₂ : ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩ < 1)
    (hK : K n ω ≤ Abound (ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩)) :
    0 ≤ ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩ - ω ⟨2, by omega⟩ - ω ⟨3, by omega⟩ ∧
      ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩ - ω ⟨2, by omega⟩ - ω ⟨3, by omega⟩ < 1 / 12 := by sorry

end KhintchineTwoRegime
