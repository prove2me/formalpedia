-- Prove2me | Theorems.Thm_MetricTesting_Characterization_structural_removability_equivalence
-- name    : MetricTesting.Characterization.structural_removability_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:26.895193+00:00
-- url     : https://prove2.me/theorems/780dcab3-797b-48f4-b7e6-211ce7dd6967
-- title:
--   Theorem 3.10 — Structural characterization of removability
-- statement:
--   For any fixed permutation-invariant local predicate on $k\ge2$ labels and any nonempty value set $\Lambda\subseteq\mathbb R_{\ge0}$, assume the associated valid matrix family is nonempty at every order $n\ge k$. Then
--   $$\Phi\text{ removable}\quad\Longleftrightarrow\quad\Phi\text{ completion stable and has packing amplification}.$$
--   All notions are uniform over every matrix order and every input array. Removability and amplification use positive extended nonnegative infima, including $+\infty$ when the indexed class is empty. Completion stability uses the right limit of the bounded real completion modulus. Both directions are asserted without extendability or measurability assumptions. The result isolates the two deterministic structural conditions underlying removal.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: infima over violation densities and minima over valid repairs → ENNReal infima with empty infimum +infinity, and attained minima of natural discrepancy counts; reason: the nonempty valid targets make the finite range of discrepancy counts attain its least element; empty far-input and packing classes retain the source convention
--   - encoding: Γ(θ) tends to zero as θ decreases to zero → for every η > 0 there is θ > 0 with Γ(θ) ≤ η; reason: Γ is nonnegative and nondecreasing on nonnegative θ, making this exactly the source right-limit condition
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 11, Theorem 3.10 (PDF p. 12)

import Definitions.Def_MetricTesting_Characterization_moduli

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Theorem 3.10, printed p.11 / PDF p.12. Neither extendability
nor measurability is needed for this deterministic characterization. -/
theorem structural_removability_equivalence (F : LocalData) (hP : TargetsNonempty F) :
    Removable F ↔ CompletionStable F ∧ PackingAmplification F := by sorry

end MetricTesting.Characterization
