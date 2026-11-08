-- Prove2me | Theorems.Thm_KhintchineTwoRegime_lemma_4
-- name    : KhintchineTwoRegime.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:33.526186+00:00
-- url     : https://prove2.me/theorems/694f1c6c-097f-4a02-ad68-c63222c594e0
-- title:
--   Lemma 4 — four-coordinate decomposition, with equality near $\omega_0=(\frac12,\frac12,\frac12,\frac12,0,\dots)$
-- statement:
--   Let $\omega\in\mathbb R^n$ with $n\ge4$, let $y=(\omega_5,\dots,\omega_n)$, and define
--   $$
--   q=\omega_1+\omega_2,\quad u=\omega_3+\omega_4,\quad d=\omega_1-\omega_2,\quad e=\omega_3-\omega_4 .
--   $$
--   Then
--   $$
--   K_n(\omega)\ \ge\ \frac38(q+u)+\frac18\bigl[\kappa(q-u;y)+\kappa(d+e;y)+\kappa(d-e;y)\bigr],
--   $$
--   with $\kappa$ as in Definition 1. Moreover, there is $\delta>0$ (depending on $n$) such that equality holds for every $\omega$ with $\|\omega-\omega_0\|_2<\delta$, where $\omega_0=(\tfrac12,\tfrac12,\tfrac12,\tfrac12,0,0,\dots)$.
--
--   The decomposition averages over the 16 sign patterns of the first four coordinates; it is the first step of Lemma 5.
--
--   **Formalization Note** The dimension is written $n=m+4$; $y_j=\omega_{j+4}$ in 0-based indexing.
--
--   Differences from the source:
--   - generalization: ω a proper vector (§2 convention); equality in a small neighborhood of ω₀ → the lower bound for every ω ∈ ℝ^{m+4}; equality for every ω in a Euclidean ball around ω₀ in ℝ^{m+4}; reason: the proof (App. A.5) uses only Jensen, the triangle inequality and the symmetry of the tail, valid for all real ω; restricting to proper vectors gives the printed lemma
--   - encoding: n ≥ 4 and y = (ω₅, …, ωₙ) → ω : Fin (m + 4) → ℝ and y j = ω (j + 4); reason: the lemma names ω₁, …, ω₄, so n ≥ 4 is implicit; same instances
--   - encoding: vectors ω ∈ ℝⁿ with the Euclidean norm ‖·‖₂, coordinates ω₁, …, ωₙ → Fin n → ℝ with the Euclidean norm √(∑ᵢ ωᵢ²) (the published HighDimProb.SparseRecovery.l2Norm), coordinates ω 0, …, ω (n−1); reason: Lean convention (Mathlib's ‖·‖ on Fin n → ℝ is the sup norm); same instances
--   - encoding: E over independent Rademacher signs → uniform average over all sign vectors Fin n → Bool (K); reason: the law of independent Rademacher signs is uniform on {−1, 1}ⁿ; same values
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), Lemma 4, p.7 (with Definition 1, p.7)

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_KhintchineTwoRegime_kappa
open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

/-- Lemma 4 (Four-coordinate decomposition) (Fang–Wang, *A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions*, arXiv:2608.27908v2 (held version of 2026-11-02, sha256 1d8d9bf1…), p.7, with Definition 1): with
`y = (ω₅, …, ωₙ)`, `q = ω₁ + ω₂`, `u = ω₃ + ω₄`, `d = ω₁ − ω₂`, `e = ω₃ − ω₄`,
`K_n(ω) ≥ (3/8)(q + u) + (1/8)[κ(q − u; y) + κ(d + e; y) + κ(d − e; y)]`, and equality holds in
a sufficiently small neighborhood of `ω₀ = (1/2, 1/2, 1/2, 1/2, 0, 0, …)`, its size depending on
`n`.

**Formalization Note** `n = m + 4`, so `ω : Fin (m + 4) → ℝ` and `y j = ω (j + 4)` (0-based).
The lower bound is stated for every real vector, not only proper ones (its proof uses only the
triangle inequality and the symmetry of the tail). The neighborhood is a Euclidean ball
`‖ω − ω₀‖₂ < δ` in `ℝ^{m+4}` with `δ > 0` depending on `m`. -/
theorem lemma_4 (m : ℕ) :
    (∀ ω : Fin (m + 4) → ℝ,
      let y : Fin m → ℝ := fun j => ω (j.addNat 4)
      let q := ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩
      let u := ω ⟨2, by omega⟩ + ω ⟨3, by omega⟩
      let d := ω ⟨0, by omega⟩ - ω ⟨1, by omega⟩
      let e := ω ⟨2, by omega⟩ - ω ⟨3, by omega⟩
      3 / 8 * (q + u) + 1 / 8 * (kappa (q - u) y + kappa (d + e) y + kappa (d - e) y) ≤
        K (m + 4) ω) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ω : Fin (m + 4) → ℝ,
      l2Norm (ω - fun i => if i.val < 4 then (1 / 2 : ℝ) else 0) < δ →
      let y : Fin m → ℝ := fun j => ω (j.addNat 4)
      let q := ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩
      let u := ω ⟨2, by omega⟩ + ω ⟨3, by omega⟩
      let d := ω ⟨0, by omega⟩ - ω ⟨1, by omega⟩
      let e := ω ⟨2, by omega⟩ - ω ⟨3, by omega⟩
      K (m + 4) ω =
        3 / 8 * (q + u) + 1 / 8 * (kappa (q - u) y + kappa (d + e) y + kappa (d - e) y)) := by sorry

end KhintchineTwoRegime
