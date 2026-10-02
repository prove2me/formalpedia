-- Prove2me | Theorems.Thm_HunterPDE_Regularity_interior_higher_regularity
-- name    : HunterPDE.Regularity.interior_higher_regularity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:42:09.322735+00:00
-- url     : https://prove2.me/theorems/47202d9a-5233-4833-aab5-768a98047442
-- title:
--   Theorem 4.28 — interior H^{k+2} regularity
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and $k \in \mathbb{N}$. Let the coefficients $a_{ij} \in C^{k+1}(\Omega) \cap L^\infty(\Omega)$ be symmetric and uniformly elliptic on $\Omega$, and let $f \in H^k(\Omega)$. If $u \in H^1(\Omega)$ is a weak solution of $Lu = -\sum_{i,j}\partial_i(a_{ij}\partial_j u) = f$ in $\Omega$, then $u \in H^{k+2}(\Omega')$ for every $\Omega' \Subset \Omega$, and
--   $$\|u\|_{H^{k+2}(\Omega')} \le C\big(\|f\|_{H^k(\Omega)} + \|u\|_{L^2(\Omega)}\big),$$
--   where the constant $C$ depends only on $n$, $k$, $\Omega'$, $\Omega$ and the $a_{ij}$.
--
--   This is the higher-order version of Theorem 4.27, obtained in the literature by iterating it; the notes state it without proof and refer to Evans.
--
--   **Formalization Note.** As in Theorem 4.27, the standing assumptions (4.17)–(4.18) are hypotheses and $C^{k+1}(\Omega)$ is `ContDiffOn ℝ (k + 1)` on $\Omega$. $H^k = W^{k,2}$ with the norm of Definition 3.23. The constant is quantified after $k$, $\Omega$, the coefficients and $\Omega'$, before $f$ and $u$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 114, Theorem 4.28

import Mathlib
import Definitions.Def_HunterPDE_Regularity_WeakSolution
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Theorem 4.28 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 114 (interior `H^{k+2}`
regularity; the notes give no proof and refer to [9], Evans): suppose `aᵢⱼ ∈ C^{k+1}(Ω)` and
`f ∈ H^k(Ω)`. If `u ∈ H¹(Ω)` is a weak solution of (4.34)–(4.35), then `u ∈ H^{k+2}(Ω′)` for every
`Ω′ ⋐ Ω`, and `‖u‖_{H^{k+2}(Ω′)} ≤ C (‖f‖_{H^k(Ω)} + ‖u‖_{L²(Ω)})` where `C` depends only on
`n`, `k`, `Ω′`, `Ω` and `aᵢⱼ`.
As in Theorem 4.27, `Ω` is open and the standing assumptions of §4.6 (`aᵢⱼ ∈ L^∞(Ω)`,
`aᵢⱼ = aⱼᵢ`, uniform ellipticity (4.18)) are hypotheses; `C^{k+1}(Ω)` is `ContDiffOn ℝ (k + 1)` on
`Ω`, and `H^k = W^{k,2}` with the norm of Definition 3.23. `C` is chosen after `k`, `Ω`, the
coefficients and `Ω′`, before `f` and `u`. -/
theorem interior_higher_regularity {n : ℕ} (k : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_C : ∀ i j, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (a i j) Ω)
    (ha_bdd : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (ha_symm : ∀ i j, a i j = a j i) (θ : ℝ) (hθ : UniformlyElliptic Ω a θ)
    (Ω' : Set (EuclideanSpace ℝ (Fin n))) (hΩ' : CompactlyContained Ω' Ω) :
    ∃ C : ℝ, ∀ f u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW k 2 Ω f → IsWeakSolution Ω a f u →
        MemW (k + 2) 2 Ω' u ∧
          sobolevNorm (k + 2) 2 Ω' u ≤ ENNReal.ofReal C *
            (sobolevNorm k 2 Ω f + eLpNorm u 2 (volume.restrict Ω)) := by sorry

end HunterPDE.Regularity
