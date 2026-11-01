-- Prove2me | Theorems.Thm_HardyCausaloid_eq27_causaloid_product
-- name    : HardyCausaloid.eq27_causaloid_product
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:40.703721+00:00
-- url     : https://prove2.me/theorems/b8cb66cf-4732-4496-bac1-8968ec3444b0
-- title:
--   Eqs. (25)–(27): the causaloid product with $\Lambda^{k_1k_2}_{l_1l_2}=r^{l_1l_2}_{k_1k_2}$, and only that $\Lambda$
-- statement:
--   Let $M$ be an experiment model, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, and $\Omega_1,\Omega_2,\Omega_{12}$ fiducial sets of $R_1,R_2,R_1\cup R_2$ with their vectors $\mathbf r_{\alpha_1}(R_1)$, $\mathbf r_{\alpha_2}(R_2)$, $\mathbf r_\alpha(R_1\cup R_2)$ (eqs. (15), (20)). For a matrix $\Lambda'^{k_1k_2}_{l_1l_2}$ ($l_1\in\Omega_1$, $l_2\in\Omega_2$, $k_1k_2\in\Omega_{12}$), the causaloid product
--   $$\big(\mathbf r_{\alpha_1}(R_1)\otimes^{\Lambda'}\mathbf r_{\alpha_2}(R_2)\big)_{k_1k_2}=\sum_{l_1l_2}r^{\alpha_1}_{l_1}r^{\alpha_2}_{l_2}\Lambda'^{k_1k_2}_{l_1l_2}\qquad(26)$$
--   equals $\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2)$ for all $\alpha_1,\alpha_2$ (eq. (27)) if and only if $\Lambda'$ is the matrix of (25),
--   $$\Lambda^{k_1k_2}_{l_1l_2}=r^{l_1l_2}_{k_1k_2}\qquad(25).$$
--
--   The matrix $\Lambda$ therefore encodes exactly the second level physical compression: knowing it, the vectors of the composite region follow from those of the components, and no other matrix does this.
--
--   Differences from the source:
--   - generalization: 'if we know Λ^{k1k2}_{l1l2} then we can calculate rα1α2(R1∪R2)' with Λ defined by (25) → the causaloid product with Λ' reproduces every r_{α₁α₂} iff Λ' is the matrix (25); reason: the ← direction is (26)–(27); the → direction adds that (25) is the only such matrix
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.3, eqs. (25)–(27), pp.13–14

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eqs. (25)–(27): the causaloid product, and the matrix `Λ` it determines**, Hardy,
arXiv:gr-qc/0608043v1, §4.3, eqs. (25)–(27), pp.13–14 ("This equation tells us that if we know
Λ^{k1k2}_{l1l2} then we can calculate rα1α2(R1∪R2) for the composite region R1 ∪ R2 from the
corresponding vectors rα1(R1) and rα2(R2) for the component regions R1 and R2.").

Let `O₁`, `O₂` be disjoint, `Ω₁`, `Ω₂`, `Ω₁₂` fiducial sets of `R₁`, `R₂`, `R₁ ∪ R₂` with their
vectors `r₁`, `r₂`, `r₁₂` (eqs. (15), (20)). For a matrix `Λ'^{k₁k₂}_{l₁l₂}`
(`l₁ ∈ Ω₁`, `l₂ ∈ Ω₂`, `k₁k₂ ∈ Ω₁₂`), the causaloid product (26)–(27) with `Λ'` reproduces every
composite vector, `r_{α₁α₂}(R₁ ∪ R₂) = r_{α₁}(R₁) ⊗^{Λ'} r_{α₂}(R₂)` for all `α₁`, `α₂`, iff
`Λ'` is the matrix of eq. (25), `Λ^{k₁k₂}_{l₁l₂} = r^{l₁l₂}_{k₁k₂}`. -/
theorem eq27_causaloid_product {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂)
    (Ω₁ : Finset (Lab Setting Outcome O₁)) (Ω₂ : Finset (Lab Setting Outcome O₂))
    (hΩ₁ : Fiducial (regionTable M O₁) Ω₁) (hΩ₂ : Fiducial (regionTable M O₂) Ω₂)
    (r₁ : Lab Setting Outcome O₁ → Ω₁ → ℝ) (r₂ : Lab Setting Outcome O₂ → Ω₂ → ℝ)
    (h₁ : ∀ α₁ s, regionTable M O₁ α₁ s = r₁ α₁ ⬝ᵥ stateVec (regionTable M O₁) Ω₁ s)
    (h₂ : ∀ α₂ s, regionTable M O₂ α₂ s = r₂ α₂ ⬝ᵥ stateVec (regionTable M O₂) Ω₂ s)
    (Ω₁₂ : Finset (Lab Setting Outcome (O₁ ∪ O₂)))
    (hΩ₁₂ : Fiducial (regionTable M (O₁ ∪ O₂)) Ω₁₂)
    (r₁₂ : Lab Setting Outcome (O₁ ∪ O₂) → Ω₁₂ → ℝ)
    (h₁₂ : ∀ α s, regionTable M (O₁ ∪ O₂) α s =
      r₁₂ α ⬝ᵥ stateVec (regionTable M (O₁ ∪ O₂)) Ω₁₂ s)
    (Λ' : Ω₁ → Ω₂ → Ω₁₂ → ℝ) :
    (∀ α₁ α₂, r₁₂ (joinLab α₁ α₂) = causaloidProduct Λ' (r₁ α₁) (r₂ α₂)) ↔
      Λ' = fun l₁ l₂ k => r₁₂ (joinLab l₁.1 l₂.1) k := by sorry

end HardyCausaloid
