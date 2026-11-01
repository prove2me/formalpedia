-- Prove2me | Theorems.Thm_HardyCausaloid_eq24_composite_functional
-- name    : HardyCausaloid.eq24_composite_functional
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:42.31599+00:00
-- url     : https://prove2.me/theorems/1b492524-a689-4a4e-9d0a-e84bbec33cc2
-- title:
--   Eq. (24): $\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)=\sum_{l_1l_2}r^{\alpha_1}_{l_1}r^{\alpha_2}_{l_2}\mathbf r_{l_1l_2}(R_1\cup R_2)$
-- statement:
--   Let $M$ be an experiment model, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, $\Omega_1,\Omega_2$ finite sets of labels of $R_1,R_2$ with vectors $\mathbf r_{\alpha_1}(R_1)$, $\mathbf r_{\alpha_2}(R_2)$ as in (15), $\Omega_{12}$ a fiducial set of $R_1\cup R_2$, and $\mathbf r_\alpha(R_1\cup R_2)\in\mathbb R^{\Omega_{12}}$ vectors with $p_\alpha=\mathbf r_\alpha(R_1\cup R_2)\cdot\mathbf p(R_1\cup R_2)$ for every label $\alpha$ of $R_1\cup R_2$ and every preparation (eq. (20)). Then for all $\alpha_1,\alpha_2$
--   $$\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)=\sum_{l_1\in\Omega_1}\sum_{l_2\in\Omega_2} r^{\alpha_1}_{l_1}\,r^{\alpha_2}_{l_2}\,\mathbf r_{l_1l_2}(R_1\cup R_2)\qquad(24),$$
--   where $l_1l_2$ runs over all of $\Omega_1\times\Omega_2$, including pairs outside $\Omega_{12}$.
--
--   So the vectors of the composite region are determined by those of the parts and by the vectors $\mathbf r_{l_1l_2}$ of the finitely many labels in $\Omega_1\times\Omega_2$; their components are the matrix $\Lambda^{k_1k_2}_{l_1l_2}$ of (25).
--
--   Differences from the source:
--   - generalization: Ω₁, Ω₂ the fiducial sets of R₁, R₂ with their vectors r → any finite sets Ω₁, Ω₂ with vectors satisfying (15) (sufficient sets); reason: the argument uses only (15) for the parts; fiducial sets are sufficient
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.3, eqs. (20), (24), p.13

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (24): the composite functional**, Hardy, arXiv:gr-qc/0608043v1, §4.3, eq. (24), p.13
("Since we can find a spanning set of linearly independent states p(R1 ∪ R2), we must have
rα1α2(R1 ∪ R2) = Σ_{l1l2} r^{α1}_{l1} r^{α2}_{l2} r_{l1l2}(R1 ∪ R2)").

Let `O₁`, `O₂` be disjoint, `Ω₁`, `Ω₂` finite sets of labels of `R₁`, `R₂` with vectors `r₁`,
`r₂` as in eq. (15), `Ω₁₂` a fiducial set of `R₁ ∪ R₂`, and `r₁₂` vectors with
`p_α = r_α(R₁ ∪ R₂) · p(R₁ ∪ R₂)` for every label `α` of `R₁ ∪ R₂` (eq. (20)). Then for all
`α₁`, `α₂`, `r_{α₁α₂} = Σ_{l₁ ∈ Ω₁} Σ_{l₂ ∈ Ω₂} r^{α₁}_{l₁} r^{α₂}_{l₂} r_{l₁l₂}`, where `l₁l₂`
runs over all of `Ω₁ × Ω₂`, including pairs outside `Ω₁₂`. -/
theorem eq24_composite_functional {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂)
    (Ω₁ : Finset (Lab Setting Outcome O₁)) (Ω₂ : Finset (Lab Setting Outcome O₂))
    (r₁ : Lab Setting Outcome O₁ → Ω₁ → ℝ) (r₂ : Lab Setting Outcome O₂ → Ω₂ → ℝ)
    (h₁ : ∀ α₁ s, regionTable M O₁ α₁ s = r₁ α₁ ⬝ᵥ stateVec (regionTable M O₁) Ω₁ s)
    (h₂ : ∀ α₂ s, regionTable M O₂ α₂ s = r₂ α₂ ⬝ᵥ stateVec (regionTable M O₂) Ω₂ s)
    (Ω₁₂ : Finset (Lab Setting Outcome (O₁ ∪ O₂)))
    (hΩ₁₂ : Fiducial (regionTable M (O₁ ∪ O₂)) Ω₁₂)
    (r₁₂ : Lab Setting Outcome (O₁ ∪ O₂) → Ω₁₂ → ℝ)
    (h₁₂ : ∀ α s, regionTable M (O₁ ∪ O₂) α s =
      r₁₂ α ⬝ᵥ stateVec (regionTable M (O₁ ∪ O₂)) Ω₁₂ s)
    (α₁ : Lab Setting Outcome O₁) (α₂ : Lab Setting Outcome O₂) :
    r₁₂ (joinLab α₁ α₂) =
      ∑ l₁ : Ω₁, ∑ l₂ : Ω₂, (r₁ α₁ l₁ * r₂ α₂ l₂) • r₁₂ (joinLab l₁.1 l₂.1) := by sorry

end HardyCausaloid
