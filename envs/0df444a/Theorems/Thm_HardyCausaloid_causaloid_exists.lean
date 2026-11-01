-- Prove2me | Theorems.Thm_HardyCausaloid_causaloid_exists
-- name    : HardyCausaloid.causaloid_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:28.05057+00:00
-- url     : https://prove2.me/theorems/b65e1eef-1ebb-4b2b-b52e-fe6915443105
-- title:
--   Eqs. (28)–(30): every model has a causaloid on any elementary fiducial sets
-- statement:
--   Let $M$ be an experiment model and, for every location $x$, let $\Omega_x$ be a fiducial set of the elementary region $R_x$. Then there is a causaloid $C$ of $M$ whose elementary fiducial sets are the given $\Omega_x$: for every finite set $O$ of locations its fiducial set $\Omega_O$ of the region $R_O$ lies in $\prod_{x\in O}\Omega_x$ (eq. (28)), and the vectors computed from its $\Lambda$ matrices by the causaloid product,
--   $$\big(\mathbf r_\alpha(R_O)\big)_k=\sum_{l\in\prod_{x\in O}\Omega_x}\Big(\prod_{x\in O}\Lambda^{l_x}_{\alpha_x}\Big)\Lambda^{k}_{l},$$
--   give every probability: $p_\alpha=\mathbf r_\alpha(R_O)\cdot\mathbf p(R_O)$ for every label $\alpha$ of $R_O$ and every generalised preparation (eq. (20)).
--
--   This is the paper's claim that "Given these Λ matrices we can calculate the r vectors for any measurement outcome for any region using the causaloid product" (p.14), with the list (30) built by second level compression for any number of regions.
--
--   Differences from the source:
--   - reading: the causaloid Λ ≡ (subset of Λ's | RULES), (31), and 'once we have the causaloid' (p.16) → a causaloid is the list (30) of Λ matrices (Causaloid) with IsCausaloidOf C M; reason: (31) leaves RULES unspecified; every compressed form is used through the list (30) it reproduces, so the theorem covers it
--   - reading: 'for any region', (28)–(30) → every finite set O of locations, with Ω_O ⊆ ∏_{x∈O} Ω_x; reason: by (2) a region is a union of elementary regions; (21) iterated through (28) places Ω_O in the product
--   - generalization: labels α₁ = 1, 2, … of (Y₁, F₁); sums over the outcomes β₂ → settings and outcomes of arbitrary types, unconditional sums (tsum/HasSum), summability proved in the conclusion; reason: the paper does not say the label sets are finite; finite label sets are the special case, where every tsum is a finite sum
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.3, eqs. (28)–(29), p.14; §4.4, eq. (30), p.14

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eqs. (28)–(30): every model has a causaloid on any elementary fiducial sets**, Hardy,
arXiv:gr-qc/0608043v1, §4.3, eqs. (28)–(29), p.14 ("We can implement second level physical
compression for more than two regions by applying the same reasoning.") and §4.4, eq. (30),
p.14 ("Given these Λ matrices we can calculate the r vectors for any measurement outcome for any
region using the causaloid product.").

For every model `M` and every family `Ω₁` of finite sets of labels with `Ω₁ x` a fiducial set of
the elementary region `R_x` for every location `x`, there is a causaloid `C` with elementary
fiducial sets `C.Ω₁ = Ω₁` that is a causaloid of `M`: its fiducial set for every region `R_O`
lies in `∏_{x∈O} Ω₁ x`, and the vectors `r_α(R_O)` computed from its Λ matrices by the causaloid
product give every probability `p_α = r_α(R_O) · p(R_O)`. -/
theorem causaloid_exists {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    (Ω₁ : ∀ x, Finset (Label Setting Outcome x))
    (hΩ₁ : ∀ x, Fiducial (elemTable M x) (Ω₁ x)) :
    ∃ C : Causaloid Setting Outcome, C.Ω₁ = Ω₁ ∧ IsCausaloidOf C M := by sorry

end HardyCausaloid
