-- Prove2me | Theorems.Thm_JointMixND_QuadOT_Supplement_theorem_6
-- name    : JointMixND.QuadOT.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:13:45.353801+00:00
-- url     : https://prove2.me/theorems/133a3834-b6a4-4732-9c55-003919f0a6fe
-- title:
--   Theorem 6, pp. 17–18 (corrected: E[W] < ∞ in the 'if' half of (i); E(ψ) nonempty) — NCD elliptical joint mixes in every dimension ⇔ Gaussian variance mixture; NOD, NSD, NA ⇔ Gaussian
-- statement:
--   Let $\psi$ be a characteristic generator, read as: the class $\mathcal E(\psi)$ of non-degenerate elliptical laws with generator $\psi$ (all positive dimensions) has a member in a positive dimension. An *NCD $n$-joint mix in $\mathcal E(\psi)$* is an $n$-dimensional member that is a joint mix, has finite second moments and has non-positive pairwise covariances.
--
--   1. (i, only if) If $\mathcal E(\psi)$ contains an NCD $n$-joint mix for every $n\ge2$, then $\mathcal E(\psi)$ is a Gaussian variance mixture family: there is a nonnegative $W$ such that every member satisfies $\mathbf X\overset d=\boldsymbol\mu+\sqrt WA\mathbf Z$.
--   2. (i, if) If $\mathcal E(\psi)$ is a Gaussian variance mixture family with mixing variable $W$ and $\mathbb E[W]<\infty$, then $\mathcal E(\psi)$ contains an NCD $n$-joint mix for every $n\ge2$.
--   3. (ii) For each of the notions NOD, NSD and NA:
--   $$\mathcal E(\psi)\text{ contains an NOD (resp. NSD, NA) $n$-joint mix for every }n\ge2\iff\text{every member of }\mathcal E(\psi)\text{ is Gaussian}.$$
--
--   The theorem separates NCD from the stronger notions. NCD joint mixes exist in all dimensions for every Gaussian variance mixture family with finite variance, such as multivariate $t$ with more than two degrees of freedom. NOD, NSD and NA joint mixes exist in all dimensions only for the Gaussian family.
--
--   **Formalization Note** NCD is strict (finite second moments, `IsStrictNCD`), because Definition 1(i) presupposes covariances. A Gaussian variance mixture family is witnessed by the law $\nu$ of $W$; $\mathbb E[W]<\infty$ is integrability of the identity under $\nu$. NSD uses the supermodular order with integrable test functions. "Gaussian" is Mathlib's `IsGaussian`.
--
--   Differences from the source:
--   - correction: Let ψ be a characteristic generator (any ψ for which (16) defines a law) → hypothesis HasNondegenerateMember ψ: E(ψ) has a member in a positive dimension; reason: for ψ ≡ 1 on ℝ₊ (the generator of point masses) E(ψ) is empty by the non-degeneracy in its definition (p. 17), so the right-hand sides 'GVM family' and 'Gaussian' hold vacuously while no n-joint mix exists: the printed 'if' halves fail; the hypothesis excludes exactly the generators whose class is empty (see DISPROOF.md)
--   - correction: (i) if E(ψ) is a Gaussian variance mixture family then it contains an NCD n-joint mix for all n ≥ 2 → the 'if' half additionally assumes E[W] < ∞ for the mixing law ν; reason: NCD presupposes covariances (Definition 1(i)); multivariate Cauchy, a Gaussian variance mixture with E[W] = ∞ and one of the t families the paper names on p. 18, has no member with finite variances, so it has no NCD joint mix; the proof on p. 30 uses that E_n(0_n, P*_n, ψ) is NCD, which needs Cov(X) = E[R²]Σ/k with E[R²] < ∞ (p. 17); see DISPROOF.md
--   - reading: NCD (Definition 1(i), Cov(X_i, X_j) ≤ 0) → IsStrictNCD: every coordinate square integrable and Cov(X_i, X_j) ≤ 0; reason: the covariances must exist; without square integrability Lean's covariance has a junk value and the notion would be vacuous for heavy-tailed members
--   - reading: (i) stated as one equivalence → two implications: 'only if' as printed and 'if' with the corrected premise; reason: the 'if' half needs the correction above; the 'only if' half holds at full strength
--   - reading: contains an NOD, NSD, or NA n-joint mix for all n ≥ 2 iff Gaussian → three separate equivalences, one per notion; reason: the proof on pp. 31–32 proves NOD and transfers to NSD and NA by Proposition 1
--   - reading: NSD: E[φ(X)] ≤ E[φ(X⊥)] for supermodular φ such that the expectations exist → φ integrable under both laws (platform SupermodularOrder); reason: 'the expectations exist' is read as finite expectations, the convention of the supermodular order
--   - encoding: X =d μ + √W A Z with W ≥ 0 independent of the standard Gaussian Z → P is the image of ν ⊗ N(0, I_k) under (w, z) ↦ μ + √w A z, with ν a probability measure, ν((−∞, 0)) = 0; reason: the representation depends only on the laws of W and Z; same instances
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, pp. 17–18, Theorem 6 (proof pp. 30–32); p. 17, definitions of E(ψ) and of Gaussian variance mixture families

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence
import Definitions.Def_JointMixND_QuadOT_Supplement_Elliptical

open MeasureTheory ProbabilityTheory

namespace JointMixND.QuadOT.Supplement

theorem theorem_6 (ψ : ℝ → ℝ) (hψ : HasNondegenerateMember ψ) :
    ((∀ n : ℕ, 2 ≤ n → ∃ P : Measure (Fin n → ℝ), InClass ψ P ∧ IsJointMix P ∧ IsStrictNCD P) →
        IsGVMFamily ψ) ∧
    ((∃ ν : Measure ℝ, IsGVMFamilyVia ψ ν ∧ Integrable (fun w => w) ν) →
        ∀ n : ℕ, 2 ≤ n → ∃ P : Measure (Fin n → ℝ), InClass ψ P ∧ IsJointMix P ∧ IsStrictNCD P) ∧
    ((∀ n : ℕ, 2 ≤ n → ∃ P : Measure (Fin n → ℝ), InClass ψ P ∧ IsJointMix P ∧ IsNOD P) ↔
        IsGaussianClass ψ) ∧
    ((∀ n : ℕ, 2 ≤ n → ∃ P : Measure (Fin n → ℝ), InClass ψ P ∧ IsJointMix P ∧ IsNSD P) ↔
        IsGaussianClass ψ) ∧
    ((∀ n : ℕ, 2 ≤ n → ∃ P : Measure (Fin n → ℝ), InClass ψ P ∧ IsJointMix P ∧ IsNA P) ↔
        IsGaussianClass ψ) := by sorry

end JointMixND.QuadOT.Supplement
