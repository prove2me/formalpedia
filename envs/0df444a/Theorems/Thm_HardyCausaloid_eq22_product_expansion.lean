-- Prove2me | Theorems.Thm_HardyCausaloid_eq22_product_expansion
-- name    : HardyCausaloid.eq22_product_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:37.205009+00:00
-- url     : https://prove2.me/theorems/6cf8e55d-1d5b-44bd-a549-a2d86dd70ca0
-- title:
--   Eq. (22): $p_{\alpha_1\alpha_2}=\sum_{l_1l_2\in\Omega_1\times\Omega_2}r^{\alpha_1}_{l_1}r^{\alpha_2}_{l_2}p_{l_1l_2}$
-- statement:
--   Let $M$ be an experiment model, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, and $\Omega_1,\Omega_2$ finite sets of labels of $R_1,R_2$ with vectors $\mathbf r_{\alpha_1}(R_1)\in\mathbb R^{\Omega_1}$, $\mathbf r_{\alpha_2}(R_2)\in\mathbb R^{\Omega_2}$ such that $p_{\alpha_1}=\mathbf r_{\alpha_1}(R_1)\cdot\mathbf p(R_1)$ and $p_{\alpha_2}=\mathbf r_{\alpha_2}(R_2)\cdot\mathbf p(R_2)$ for every label and every generalised preparation (eq. (15)). Then for all labels $\alpha_1,\alpha_2$ and every generalised preparation in $R-R_1-R_2$,
--   $$p_{\alpha_1\alpha_2}=\sum_{l_1\in\Omega_1}\sum_{l_2\in\Omega_2} r^{\alpha_1}_{l_1}\,r^{\alpha_2}_{l_2}\,p_{l_1l_2}\qquad(22).$$
--
--   The probabilities of the composite region are thus linear in the $|\Omega_1||\Omega_2|$ probabilities $p_{l_1l_2}$, which is what makes $\Omega_1\times\Omega_2$ a sufficient set for $R_1\cup R_2$ (eq. (21)). No product form of the probabilities is assumed.
--
--   Differences from the source:
--   - generalization: Ω₁, Ω₂ the fiducial sets of R₁, R₂ with their vectors r → any finite sets Ω₁, Ω₂ with vectors satisfying (15) (sufficient sets); reason: the argument uses only (15) for the parts; fiducial sets are sufficient
--   - encoding: a generalised preparation (Y_{R−R₁−R₂}, F_{R−R₁−R₂}) in R − R₁ − R₂ → a total label s whose values on the region are ignored (it enters only through glue); reason: the labels of R off the region are exactly the generalised preparations; same instances
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.3, eqs. (22)–(23), p.13

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (22): `p_{α₁α₂}` expands over `Ω₁ × Ω₂`**, Hardy, arXiv:gr-qc/0608043v1, §4.3, eqs.
(22)–(23), p.13 ("Now we note from (22) that pα1α2 is given by a linear sum over the
probabilities pl1l2 where l1l2 ∈ Ω1 × Ω2.").

Let `O₁`, `O₂` be disjoint finite sets of locations, `Ω₁`, `Ω₂` finite sets of labels of the
regions `R₁ = R_{O₁}`, `R₂ = R_{O₂}`, and `r₁`, `r₂` vectors with `p_{α₁} = r_{α₁}(R₁) · p(R₁)`
and `p_{α₂} = r_{α₂}(R₂) · p(R₂)` for every label and every generalised preparation (eq. (15)).
Then for all `α₁`, `α₂` and every generalised preparation `s` in `R − R₁ − R₂`,
`p_{α₁α₂} = Σ_{l₁ ∈ Ω₁} Σ_{l₂ ∈ Ω₂} r^{α₁}_{l₁} r^{α₂}_{l₂} p_{l₁l₂}`.

**Formalization Note** No product form of the probabilities is assumed. -/
theorem eq22_product_expansion {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂)
    (Ω₁ : Finset (Lab Setting Outcome O₁)) (Ω₂ : Finset (Lab Setting Outcome O₂))
    (r₁ : Lab Setting Outcome O₁ → Ω₁ → ℝ) (r₂ : Lab Setting Outcome O₂ → Ω₂ → ℝ)
    (h₁ : ∀ α₁ s, regionTable M O₁ α₁ s = r₁ α₁ ⬝ᵥ stateVec (regionTable M O₁) Ω₁ s)
    (h₂ : ∀ α₂ s, regionTable M O₂ α₂ s = r₂ α₂ ⬝ᵥ stateVec (regionTable M O₂) Ω₂ s)
    (α₁ : Lab Setting Outcome O₁) (α₂ : Lab Setting Outcome O₂)
    (s : ∀ x, Label Setting Outcome x) :
    regionTable M (O₁ ∪ O₂) (joinLab α₁ α₂) s =
      ∑ l₁ : Ω₁, ∑ l₂ : Ω₂,
        r₁ α₁ l₁ * r₂ α₂ l₂ * regionTable M (O₁ ∪ O₂) (joinLab l₁.1 l₂.1) s := by sorry

end HardyCausaloid
