-- Prove2me | Theorems.Thm_HardyCausaloid_eq21_fiducial_subset_product
-- name    : HardyCausaloid.eq21_fiducial_subset_product
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:37.578525+00:00
-- url     : https://prove2.me/theorems/77fa9227-8d0e-4e13-8add-e8a0c4ae3113
-- title:
--   Eq. (21): a fiducial set $\Omega_{12}\subseteq\Omega_1\times\Omega_2$ exists
-- statement:
--   Let $M$ be an experiment model, $O_1,O_2$ disjoint finite sets of locations with regions $R_1,R_2$, and $\Omega_1,\Omega_2$ sufficient finite sets of labels of $R_1,R_2$. Then the composite region $R_1\cup R_2$ has a fiducial set
--   $$\Omega_{12}\subseteq\Omega_1\times\Omega_2\qquad(21),$$
--   that is, every element of $\Omega_{12}$ is a joint label $l_1l_2$ with $l_1\in\Omega_1$ and $l_2\in\Omega_2$.
--
--   The paper calls this result "central to the method": it lets the fiducial sets of all composite regions be built from those of the elementary regions. Second level physical compression is nontrivial when the inclusion is proper; the statement makes no claim either way.
--
--   Differences from the source:
--   - generalization: Ω₁, Ω₂ the fiducial sets of R₁, R₂ with their vectors r → any finite sets Ω₁, Ω₂ with vectors satisfying (15) (sufficient sets); reason: the argument uses only (15) for the parts; fiducial sets are sufficient
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
--   - encoding: Ω₁₂ ⊆ Ω₁ × Ω₂ → every k ∈ Ω₁₂ is joinLab l₁ l₂ with l₁ ∈ Ω₁, l₂ ∈ Ω₂; reason: a label of R₁ ∪ R₂ is the pair of its restrictions; same sets
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.3, eq. (21), p.13

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

/-- **Eq. (21): a fiducial set of the composite region inside `Ω₁ × Ω₂`**, Hardy,
arXiv:gr-qc/0608043v1, §4.3, eq. (21), p.13 ("We will now prove that there always exists a
choice of fiducial set Ω12 such that Ω12 ⊆ Ω1 × Ω2").

Let `O₁`, `O₂` be disjoint finite sets of locations and `Ω₁`, `Ω₂` sufficient finite sets of
labels of the regions `R₁`, `R₂`. Then the composite region `R₁ ∪ R₂` has a fiducial set
`Ω₁₂` every element of which is a joint label `l₁l₂` with `l₁ ∈ Ω₁` and `l₂ ∈ Ω₂`.

**Formalization Note** `Ω₁₂ ⊆ Ω₁ × Ω₂` is written through the joint label `joinLab l₁ l₂`; no
claim is made that the inclusion is proper (compression may or may not occur). -/
theorem eq21_fiducial_subset_product {X : Type*} {Setting : X → Type*}
    {Outcome : (x : X) → Setting x → Type*} [DecidableEq X] (M : Model Setting Outcome)
    {O₁ O₂ : Finset X} (hO : Disjoint O₁ O₂)
    (Ω₁ : Finset (Lab Setting Outcome O₁)) (Ω₂ : Finset (Lab Setting Outcome O₂))
    (h₁ : Sufficient (regionTable M O₁) Ω₁) (h₂ : Sufficient (regionTable M O₂) Ω₂) :
    ∃ Ω₁₂ : Finset (Lab Setting Outcome (O₁ ∪ O₂)),
      (∀ k ∈ Ω₁₂, ∃ l₁ ∈ Ω₁, ∃ l₂ ∈ Ω₂, k = joinLab l₁ l₂) ∧
      Fiducial (regionTable M (O₁ ∪ O₂)) Ω₁₂ := by sorry

end HardyCausaloid
