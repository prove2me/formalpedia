-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_4_2
-- name    : JainCRERepetition.Cubic.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:45.59777+00:00
-- url     : https://prove2.me/theorems/f6449e63-cfa7-431f-87ec-af9d7368eb20
-- title:
--   Lemma 4.2 — constructive marginal replacement
-- statement:
--   Let $\rho^{RK}$ be a state and $\nu^{RK}$ a nonzero positive operator, possibly unnormalized, with finite $D(\rho\|\nu)$. Define $L_s=(\rho^K)^{(1+is)/2}(\nu^K)^{-(1+is)/2}$ using inverse powers on the support, zero on the kernel, and put
--
--   $$\widetilde\nu=\int_{\mathbb R}\beta_0(s)(1_R\otimes L_s)\nu(1_R\otimes L_s)^\dagger ds.$$
--
--   This exact integral is a density operator, with $\widetilde\nu^K=\rho^K$ and $D_M(\rho\|\widetilde\nu)\le D(\rho\|\nu)-D(\rho^K\|\nu^K)$. It depends on the target only through $\rho^K$. If $R=\widehat X\widehat Y$, $K=XA$, the target has matching-copy support, and $\nu$ is an Alice conditional comparison, then the same replacement remains an Alice conditional comparison. No full-support or smallest-eigenvalue hypothesis is imposed.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - encoding: a finite-dimensional operator integral → entrywise complex Lebesgue integrals with integrability asserted; reason: finite matrix integration is entrywise, and the support-general trace-one integrands are absolutely integrable against beta0
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 27–28, Lemma 4.2, Eqs. (39)–(41); p. 37, Appendix D; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_allocation

open scoped ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_4_2 :
    (∀ (R K : Type) [Fintype R] [Fintype K] [DecidableEq R] [DecidableEq K]
      (ρ ν : Op (R × K)), IsState ρ → ν.PosSemidef → ν ≠ 0 → FiniteD ρ ν →
      (∀ a b, MeasureTheory.Integrable (fun s : ℝ => replacementKernel ρ ν s a b)) ∧
      IsState (replacement ρ ν) ∧ trL (replacement ρ ν) = trL ρ ∧
      MeasuredD ρ (replacement ρ ν) ≤ (d ρ ν - d (trL ρ) (trL ν) : ℝ) ∧
      (∀ ρ' : Op (R × K), IsState ρ' → FiniteD ρ' ν →
        trL ρ' = trL ρ → replacement ρ' ν = replacement ρ ν)) ∧
    (∀ (X Y A : Type) [Fintype X] [Fintype Y] [Fintype A]
      [DecidableEq X] [DecidableEq Y] [DecidableEq A]
      (μ : Law (X × Y)) (ρ ν : Op (AliceIndex X Y A)),
      IsState ρ → copyMatching ρ → IsComparison μ ν → FiniteD ρ ν →
      IsState (replacement ρ ν) ∧ IsComparison μ (replacement ρ ν) ∧
      trL (replacement ρ ν) = trL ρ ∧
      MeasuredD ρ (replacement ρ ν) ≤ (charge ρ ν : ℝ)) := by sorry
end JainCRERepetition.Cubic
