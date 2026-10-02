-- Prove2me | Theorems.Thm_HunterPDE_Regularity_interior_H2_regularity
-- name    : HunterPDE.Regularity.interior_H2_regularity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:38:17.545624+00:00
-- url     : https://prove2.me/theorems/13300b40-c9bb-4c66-b1b1-22f4017c0539
-- title:
--   Theorem 4.27 — interior H² regularity of weak solutions of −∑∂ᵢ(aᵢⱼ∂ⱼu) = f
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. Let the coefficients $a_{ij} \in C^1(\Omega) \cap L^\infty(\Omega)$ be symmetric, $a_{ij} = a_{ji}$, and uniformly elliptic on $\Omega$ with constant $\theta > 0$, and let $f \in L^2(\Omega)$. If $u \in H^1(\Omega)$ is a weak solution of $Lu = -\sum_{i,j}\partial_i(a_{ij}\partial_j u) = f$ in $\Omega$, then $u \in H^2(\Omega')$ for every $\Omega' \Subset \Omega$, and
--   $$\|u\|_{H^2(\Omega')} \le C\big(\|f\|_{L^2(\Omega)} + \|u\|_{L^2(\Omega)}\big),$$
--   where the constant $C$ depends only on $n$, $\Omega'$, $\Omega$ and the $a_{ij}$ — not on $f$ or $u$.
--
--   Weak solutions are a priori only in $H^1$; this theorem shows they have square-integrable second weak derivatives away from the boundary, so that the equation holds pointwise almost everywhere (a strong solution).
--
--   **Formalization Note.** The hypotheses $a_{ij} \in L^\infty(\Omega)$, $a_{ij} = a_{ji}$ and uniform ellipticity are the standing assumptions (4.17)–(4.18) of §4.6 on the operator. $C^1(\Omega)$ is `ContDiffOn ℝ 1` on $\Omega$, as printed (no regularity up to the boundary). The constant is `∃ C : ℝ`, quantified after $\Omega$, the coefficients, $\theta$ and $\Omega'$ and before $f$ and $u$; the norms are `ℝ≥0∞`-valued and $C$ enters as `ENNReal.ofReal C`. $\|u\|_{H^2(\Omega')}$ is the norm of Definition 3.23 with $k = 2$, $p = 2$ and weak derivatives on $\Omega'$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 112, Theorem 4.27

import Mathlib
import Definitions.Def_HunterPDE_Regularity_WeakSolution
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Theorem 4.27 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 112 (interior `H²`
regularity): let `Ω` be an open set in `ℝⁿ`, `aᵢⱼ ∈ C¹(Ω)` and `f ∈ L²(Ω)`. If `u ∈ H¹(Ω)` is a
weak solution of `L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu) = f` ((4.34)–(4.37)), then `u ∈ H²(Ω′)` for every
`Ω′ ⋐ Ω`, and (4.39) `‖u‖_{H²(Ω′)} ≤ C (‖f‖_{L²(Ω)} + ‖u‖_{L²(Ω)})` where `C` depends only on
`n`, `Ω′`, `Ω` and `aᵢⱼ`.
The standing assumptions of §4.6 on `L` are hypotheses: `aᵢⱼ ∈ L^∞(Ω)`, `aᵢⱼ = aⱼᵢ` ((4.17)) and
uniform ellipticity with constant `θ` ((4.18)). `C¹(Ω)` is `ContDiffOn ℝ 1` on `Ω` (no
regularity up to the boundary, as printed). The constant `C` is chosen after `Ω`, the
coefficients (and their ellipticity constant) and `Ω′`, and before `f` and `u`. -/
theorem interior_H2_regularity {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_C1 : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (ha_bdd : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (ha_symm : ∀ i j, a i j = a j i) (θ : ℝ) (hθ : UniformlyElliptic Ω a θ)
    (Ω' : Set (EuclideanSpace ℝ (Fin n))) (hΩ' : CompactlyContained Ω' Ω) :
    ∃ C : ℝ, ∀ f u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp f 2 (volume.restrict Ω) → IsWeakSolution Ω a f u →
        MemW 2 2 Ω' u ∧
          sobolevNorm 2 2 Ω' u ≤ ENNReal.ofReal C *
            (eLpNorm f 2 (volume.restrict Ω) + eLpNorm u 2 (volume.restrict Ω)) := by sorry

end HunterPDE.Regularity
