-- Prove2me | Theorems.Thm_HunterPDE_Compactness_rellich_kondrachov
-- name    : HunterPDE.Compactness.rellich_kondrachov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:26:18.88488+00:00
-- url     : https://prove2.me/theorems/417b0f64-925f-4f9b-8e08-588f33ec9722
-- title:
--   Theorem 3.45 — Rellich–Kondrachov: bounded sets in W^{1,p}_0(Ω) are precompact in L^q
-- statement:
--   Let $\Omega$ be a bounded open set in $\mathbb{R}^n$, $1 \le p < n$, and $1 \le q < p^* = \dfrac{np}{n-p}$. If $\mathcal{F}$ is a bounded set in $W^{1,p}_0(\Omega)$, that is, $\|f\|_{W^{1,p}(\Omega)} \le M$ for all $f \in \mathcal{F}$, then $\mathcal{F}$ is precompact in $L^q(\mathbb{R}^n)$:
--   $$\overline{\{\, f \mathbf{1}_\Omega : f \in \mathcal{F} \,\}} \ \text{ is compact in } L^q(\mathbb{R}^n).$$
--
--   Equivalently, every bounded sequence in $W^{1,p}_0(\Omega)$ has a subsequence converging in $L^q$. This compact embedding underlies the Fredholm theory and spectral theory of elliptic operators on bounded domains. Both boundedness of $\Omega$ and $q < p^*$ are necessary.
--
--   **Formalization Note.** $p$ is real with $1 \le p < n$, and $q \in [1, \infty]$ with $q < p^*$ (so $q$ is finite). Elements of $\mathcal{F}$ are functions $\mathbb{R}^n \to \mathbb{R}$ in `MemW0 1 p Ω` with a common bound on `sobolevNorm 1 p Ω`. They are placed in $L^q(\mathbb{R}^n)$ by extension by zero, `Ω.indicator f`. The conclusion states that every extension is in $L^q$, and that the set of their classes in Mathlib's `Lp ℝ q volume` has compact closure.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 73, Theorem 3.45

import Mathlib
import Definitions.Def_HunterPDE_Compactness_Sobolev

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Compactness

/-- Theorem 3.45 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 73 (Rellich–Kondrachov): let
`Ω` be a bounded open set in `ℝⁿ`, `1 ≤ p < n` and `1 ≤ q < p* = np/(n − p)`. If `F` is a bounded
set in `W^{1,p}_0(Ω)`, then `F` is precompact in `L^q(ℝⁿ)`.
Elements of `F` are functions `ℝⁿ → ℝ` in `W^{1,p}_0(Ω)` (closure of `C_c^∞(Ω)` in the
`W^{1,p}(Ω)` norm) with a common bound on `‖f‖_{W^{1,p}(Ω)}`; they are placed in `L^q(ℝⁿ)` by
extension by zero outside `Ω` (`Ω.indicator f`). The conclusion says every extension lies in
`L^q(ℝⁿ)` and the set of their classes has compact closure in `L^q(ℝⁿ)`. -/
theorem rellich_kondrachov {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hp : 1 ≤ p) (hpn : p < n)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q < ENNReal.ofReal (sobolevConjugate n p))
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hF : ∀ f ∈ F, MemW0 1 (ENNReal.ofReal p) Ω f)
    (hFb : ∃ M : ℝ≥0, ∀ f ∈ F, sobolevNorm 1 (ENNReal.ofReal p) Ω f ≤ (M : ℝ≥0∞)) :
    (∀ f ∈ F, MemLp (Ω.indicator f) q volume) ∧
      IsCompact (closure {u : Lp ℝ q (volume : Measure (EuclideanSpace ℝ (Fin n))) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] Ω.indicator f}) := by sorry

end HunterPDE.Compactness
