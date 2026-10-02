-- Prove2me | Theorems.Thm_HunterPDE_Regularity_interior_smoothness
-- name    : HunterPDE.Regularity.interior_smoothness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:45:32.014288+00:00
-- url     : https://prove2.me/theorems/d11ff9fb-6cec-47f2-b51a-bc397e64586b
-- title:
--   Corollary 4.29 — weak solutions with smooth coefficients and data are smooth
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, let the coefficients $a_{ij} \in C^\infty(\Omega) \cap L^\infty(\Omega)$ be symmetric and uniformly elliptic on $\Omega$, and let $f \in C^\infty(\Omega) \cap L^2(\Omega)$. If $u \in H^1(\Omega)$ is a weak solution of $Lu = -\sum_{i,j}\partial_i(a_{ij}\partial_j u) = f$ in $\Omega$, then
--   $$u \in C^\infty(\Omega),$$
--   that is, $u$ agrees almost everywhere in $\Omega$ with a function that is infinitely differentiable in $\Omega$.
--
--   This is interior elliptic regularity in its qualitative form: weak solutions of equations with smooth coefficients and data are classical solutions.
--
--   **Formalization Note.** $f \in L^2(\Omega)$ is the standing assumption of §4.11 ((4.34)), under which the weak formulation is defined; $a_{ij} \in L^\infty(\Omega)$, $a_{ij} = a_{ji}$ and uniform ellipticity are those of §4.6. $C^\infty$ is `ContDiffOn ℝ ∞` (smooth, not analytic).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 114, Corollary 4.29

import Mathlib
import Definitions.Def_HunterPDE_Regularity_WeakSolution

open MeasureTheory
open scoped ENNReal ContDiff

namespace HunterPDE.Regularity

/-- Corollary 4.29 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 114: if `aᵢⱼ, f ∈ C^∞(Ω)`
and `u ∈ H¹(Ω)` is a weak solution of (4.34)–(4.35), then `u ∈ C^∞(Ω)`, i.e. `u` agrees almost
everywhere on `Ω` with a function that is infinitely differentiable on `Ω`.
`Ω` is open; the standing assumptions of §4.6 and §4.11 are hypotheses: `f ∈ L²(Ω)` ((4.34)),
`aᵢⱼ ∈ L^∞(Ω)`, `aᵢⱼ = aⱼᵢ` ((4.17)), uniform ellipticity (4.18). `C^∞` is
`ContDiffOn ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, not analytic). -/
theorem interior_smoothness {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_smooth : ∀ i j, ContDiffOn ℝ ∞ (a i j) Ω)
    (ha_bdd : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (ha_symm : ∀ i j, a i j = a j i) (θ : ℝ) (hθ : UniformlyElliptic Ω a θ)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) (hf_smooth : ContDiffOn ℝ ∞ f Ω)
    (hf : MemLp f 2 (volume.restrict Ω)) (hu : IsWeakSolution Ω a f u) :
    ∃ w : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ ∞ w Ω ∧ u =ᵐ[volume.restrict Ω] w := by sorry

end HunterPDE.Regularity
