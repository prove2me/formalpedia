-- Prove2me | Theorems.Thm_HardyCausaloid_fiducial_spanning_states
-- name    : HardyCausaloid.fiducial_spanning_states
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:44.261053+00:00
-- url     : https://prove2.me/theorems/3b54c688-1ca9-421f-a776-9e80955bf67a
-- title:
--   §4.2, p.12: a fiducial set has $|\Omega_1|$ linearly independent states
-- statement:
--   Let $q(\alpha,s)$ be a table of real numbers and $\Omega$ a fiducial set for it, with state vectors $\mathbf p(s)=(q(l,s))_{l\in\Omega}\in\mathbb R^\Omega$. Then
--
--   1. the state vectors $\mathbf p(s)$, over all preparations $s$, span $\mathbb R^{\Omega}$;
--   2. there are preparations $s_l$, $l\in\Omega$, whose states $\mathbf p(s_l)$ are linearly independent — $|\Omega|$ linearly independent states;
--   3. for every label $\alpha$ the vector $\mathbf r_\alpha$ with $q(\alpha,s)=\mathbf r_\alpha\cdot\mathbf p(s)$ for all $s$ exists and is unique.
--
--   This is the fact the paper invokes at (24) ("Since we can find a spanning set of linearly independent states") and at (36) ("since there exists a linearly independent spanning set of such states").
--
--   Differences from the source:
--   - generalization: the probabilities p_α of the labels α of a region R₁ under the generalised preparations in R − R₁ → any real table q α s; reason: the statement is linear algebra on the table; it specializes to q = regionTable M O and q = elemTable M x
--   - generalization: there must exist a set of |Ω₁| linearly independent states → the states span ℝ^Ω, |Ω| of them are linearly independent, and the vectors r_α are unique; reason: adds the spanning and uniqueness consequences the paper uses at (24) and (36); clause 2 is the page's claim
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.2, p.12

import Mathlib
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

/-- **A just sufficient list has `|Ω|` linearly independent states**, Hardy,
arXiv:gr-qc/0608043v1, §4.2, p.12 ("Since the probabilities in p(R1) are just sufficient for this
purpose, there must exist a set of |Ω1| linearly independent states chosen from the allowed set
of states.").

If `Ω` is a fiducial set of the probability table `q`, then

1. the state vectors `p_Ω(s)`, over all generalised preparations `s`, span `ℝ^Ω`;
2. some `|Ω|` of them, `p_Ω(s_l)` for `l ∈ Ω`, are linearly independent;
3. for every label `α` the vector `r_α` of eq. (15) is unique.

**Formalization Note** The table is arbitrary; the paper's case is `q = regionTable M O` (or
`elemTable M x`). -/
theorem fiducial_spanning_states {A S : Type*} (q : A → S → ℝ) (Ω : Finset A)
    (hΩ : Fiducial q Ω) :
    Submodule.span ℝ (Set.range (stateVec q Ω)) = ⊤ ∧
    (∃ s : Ω → S, LinearIndependent ℝ (fun l => stateVec q Ω (s l))) ∧
    (∀ α : A, ∃! r : Ω → ℝ, ∀ s : S, q α s = r ⬝ᵥ stateVec q Ω s) := by sorry

end HardyCausaloid
