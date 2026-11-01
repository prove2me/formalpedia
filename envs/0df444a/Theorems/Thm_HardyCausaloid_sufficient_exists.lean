-- Prove2me | Theorems.Thm_HardyCausaloid_sufficient_exists
-- name    : HardyCausaloid.sufficient_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:47.393827+00:00
-- url     : https://prove2.me/theorems/cd045681-e674-489c-8fe1-b9ee0525c2e9
-- title:
--   §4.2, (13)–(15): a finite sufficient list exists and contains a fiducial one
-- statement:
--   Let $q(\alpha,s)$ be a table of real numbers indexed by labels $\alpha\in A$ and preparations $s\in S$; its **states** are the vectors $(q(\alpha,s))_{\alpha\in A}\in\mathbb R^A$, one for each $s$.
--
--   1. The states span a finite-dimensional subspace of $\mathbb R^A$ if and only if some finite set $\Omega\subseteq A$ is sufficient for $q$.
--   2. Every sufficient finite set contains a fiducial (just sufficient) subset.
--   3. If $A$ is finite, $A$ itself is sufficient (eq. (13), $p_\alpha=\mathbf R_\alpha\cdot\mathbf P$ with $\mathbf R_\alpha$ the unit vector).
--
--   This is the claim "Clearly this is possible since, as a last resort, we have (13)" on p.12: the fiducial set of every region exists, and it is what first level physical compression starts from.
--
--   Differences from the source:
--   - generalization: the probabilities p_α of the labels α of a region R₁ under the generalised preparations in R − R₁ → any real table q α s; reason: the statement is linear algebra on the table; it specializes to q = regionTable M O and q = elemTable M x
--   - generalization: 'Clearly this is possible since, as a last resort, we have (13)' (a just sufficient list exists when the labels are listed) → finite-dimensional span of the states ↔ a finite sufficient set exists; every sufficient set contains a fiducial one; for finitely many labels all labels are sufficient (13); reason: covers infinite label sets (finitely many labels is clause 3 with clause 2); it specializes to the paper's claim
--   - reading: a just sufficient set of probabilities (p.11), the fiducial set (p.12) → Fiducial: sufficient, and no proper subset is sufficient; reason: inclusion-minimality is the literal sense of just sufficient
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.2, eqs. (13)–(15), pp.11–12

import Mathlib
import Definitions.Def_HardyCausaloid_Fiducial

set_option autoImplicit false

namespace HardyCausaloid

/-- **A finite sufficient list exists, and it can be cut down to a fiducial one**, Hardy,
*Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal
Structure*, arXiv:gr-qc/0608043v1, §4.2, eqs. (13)–(15), pp.11–12 ("Clearly this is possible
since, as a last resort, we have (13).").

For a probability table `q α s` (labels `α : A`, generalised preparations `s : S`):

1. the states `s ↦ (q α s)_α` span a finite-dimensional subspace of `ℝ^A` iff some finite set
   of labels is sufficient;
2. every sufficient finite set contains a fiducial (just sufficient) one;
3. if there are finitely many labels, the set of all labels is sufficient (eq. (13)).

**Formalization Note** The table is arbitrary; the paper's case is
`q = regionTable M O` (or `elemTable M x`), with `A` the labels of the region and `S` the total
labels. -/
theorem sufficient_exists {A S : Type*} (q : A → S → ℝ) :
    (FiniteDimensional ℝ (Submodule.span ℝ (Set.range (fun s : S => fun α : A => q α s))) ↔
      ∃ Ω : Finset A, Sufficient q Ω) ∧
    (∀ Ω : Finset A, Sufficient q Ω → ∃ Ω' ⊆ Ω, Fiducial q Ω') ∧
    (∀ [Fintype A], Sufficient q Finset.univ) := by sorry

end HardyCausaloid
