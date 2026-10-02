-- Prove2me | Theorems.Thm_HunterPDE_Friedrichs_friedrichs_commutator
-- name    : HunterPDE.Friedrichs.friedrichs_commutator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:58:34.400996+00:00
-- url     : https://prove2.me/theorems/5f666fc4-1bab-4a0b-8bff-b2233895b10f
-- title:
--   Lemma 8.11 — Friedrichs' commutator lemma: [J_ε, L] is uniformly bounded on L²(ℝⁿ) and tends to 0 strongly
-- statement:
--   Let $\eta$ be a mollifier profile on $\mathbb{R}^n$ (compactly supported, non-negative, radially symmetric, $C^\infty$, unit integral), $\eta_\varepsilon(x) = \varepsilon^{-n}\eta(x/\varepsilon)$, and $J_\varepsilon u = \eta_\varepsilon * u$ the smoothing operator (8.13). Let $L = A^i\partial_i + C$ as in (8.3) with coefficients $A^i \in C^1_c(\mathbb{R}^n;\mathbb{R}^{m\times m})$ and $C \in C_c(\mathbb{R}^n;\mathbb{R}^{m\times m})$. Then for each $\varepsilon > 0$ the commutator
--   $$[J_\varepsilon, L] = J_\varepsilon L - L J_\varepsilon : C^1_c(\mathbb{R}^n;\mathbb{R}^m) \to L^2(\mathbb{R}^n;\mathbb{R}^m)$$
--   extends to a bounded linear operator $\overline{[J_\varepsilon, L]} : L^2(\mathbb{R}^n;\mathbb{R}^m) \to L^2(\mathbb{R}^n;\mathbb{R}^m)$, there is $K$ with $\|\overline{[J_\varepsilon,L]}\| \le K$ for all $\varepsilon > 0$, and for every $u \in L^2(\mathbb{R}^n;\mathbb{R}^m)$
--   $$\overline{[J_\varepsilon, L]}\,u \to 0 \quad \text{in } L^2(\mathbb{R}^n;\mathbb{R}^m) \text{ as } \varepsilon \to 0^+ .$$
--   This is the tool behind Friedrichs' "weak equals strong" theorem (Theorem 8.12 of the notes): it lets one mollify a weak solution and control the error in the equation.
--
--   **Formalization Note.** The extensions form a family `T : ℝ → (L² →L[ℝ] L²)` (values at $\varepsilon \le 0$ are unconstrained); "extends" means that for $\varepsilon > 0$ and every $u \in C^1_c$, `T ε` applied to the $L^2$ class of $u$ agrees a.e. with the pointwise commutator. Since $C^1_c$ is dense in $L^2$, each `T ε` is uniquely determined. The lemma is stated for every mollifier profile, which includes the specific bump (1.5); coordinates are 0-based, and $\mathbb{R}^m$ carries the Euclidean norm.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 228, Lemma 8.11

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_Mollifier

open MeasureTheory Filter Topology

namespace HunterPDE.Friedrichs

/-- Hunter, *Notes on PDEs* (revised 6/18/2014), Lemma 8.11 (Friedrichs), p. 228. Let `η` be a
mollifier profile (compactly supported, non-negative, radially symmetric, `C^∞`, unit integral),
`J_ε u = η_ε ∗ u` the smoothing operator (8.13), and `L = Aⁱ∂ᵢ + C` the operator (8.3) with
`Aⁱ ∈ C¹_c(ℝⁿ; ℝ^{m×m})` and `C ∈ C_c(ℝⁿ; ℝ^{m×m})`. Then for each `ε > 0` the commutator
`[J_ε, L] = J_ε L − L J_ε : C¹_c(ℝⁿ; ℝᵐ) → L²(ℝⁿ; ℝᵐ)` extends to a bounded linear operator
`T ε` on `L²(ℝⁿ; ℝᵐ)`, the operator norms `‖T ε‖` are bounded uniformly in `ε > 0`, and
`T ε u → 0` in `L²` as `ε → 0⁺` for every `u ∈ L²(ℝⁿ; ℝᵐ)`. -/
theorem friedrichs_commutator {n m : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : IsMollifierProfile η)
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (∀ j k, ContDiff ℝ 1 (fun x => A i x j k)) ∧ HasCompactSupport (A i))
    (hC : (∀ j k, Continuous (fun x => C x j k)) ∧ HasCompactSupport C) :
    ∃ T : ℝ → (Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      (∀ ε : ℝ, 0 < ε → ∀ u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
        ∀ hu : MemLp u 2 volume, ContDiff ℝ 1 u → HasCompactSupport u →
          (T ε (hu.toLp u) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
            =ᵐ[volume] commutator η ε A C u) ∧
      (∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ‖T ε‖ ≤ K) ∧
      (∀ u : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun ε => T ε u) (𝓝[>] 0) (𝓝 0)) := by sorry

end HunterPDE.Friedrichs
