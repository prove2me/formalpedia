-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_7
-- name    : JainCRERepetition.Cubic.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:07.563224+00:00
-- url     : https://prove2.me/theorems/4814be49-8ee8-41d0-8c81-f3d9c35d344e
-- title:
--   Lemma 2.7 — equivalent conditional-comparison forms
-- statement:
--   An Alice conditional comparison $\nu_A$ for $\mu$ is equivalently obtained from a distribution $r_X$ supported on $\mu_X$ and unit vectors $\xi_x$ on a finite $A\otimes F$ by tracing $YF$ from
--
--   $$|\xi\rangle=\sum_{x,y}\sqrt{r_X(x)\mu(y\mid x)}|xx\rangle|yy\rangle|\xi_x\rangle.$$
--
--   Both directions hold. Every density-form seed $\tau_A$ has the same retained $XA$ marginal as its comparison; in a purification representation this marginal is $\sum_xr_X(x)|x\rangle\langle x|\otimes\xi_x^A$. The symmetric Bob characterization is the same universally quantified statement with the question/workspace alphabets interchanged. In particular $r_X$ is free and need not equal the target marginal.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
--   - encoding: a finite purifying system and the symmetric Bob statement → Fin k purifiers and a statement uniform over both alphabet roles; reason: every finite basis is equivalent to Fin k; swapping the quantified labels gives the full Bob characterization
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 12, Lemma 2.7, Eq. (5); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_copied

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_7
    {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A]
    (μ : Law (X × Y)) :
    (∀ ν : Op (AliceIndex X Y A), IsState ν →
      (IsComparison μ ν ↔ ∃ (k : ℕ) (r : Law X) (ξ : X → A × Fin k → ℂ),
        (∀ x, marginalX μ.p x = 0 → r.p x = 0) ∧
        (∀ x, IsUnit (ξ x)) ∧ ν = purifiedComparison μ r ξ)) ∧
    (∀ τ : Op (X × (X × A)), IsState τ → seedMatching τ →
      (∀ x, marginalX μ.p x = 0 → ∀ a, τ (x,(x,a)) (x,(x,a)) = 0) →
      trL (comparison μ τ) = trL τ) ∧
    (∀ (k : ℕ) (r : Law X) (ξ : X → A × Fin k → ℂ),
      (∀ x, marginalX μ.p x = 0 → r.p x = 0) → (∀ x, IsUnit (ξ x)) →
      trL (purifiedComparison μ r ξ) = cq r.p (fun x => trR (ket (ξ x)))) := by sorry
end JainCRERepetition.Cubic
