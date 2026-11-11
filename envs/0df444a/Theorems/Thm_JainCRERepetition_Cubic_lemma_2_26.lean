-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_26
-- name    : JainCRERepetition.Cubic.lemma_2_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:52.820761+00:00
-- url     : https://prove2.me/theorems/15e687b3-4782-4751-80f5-438282499620
-- title:
--   Lemma 2.26 — information controlled by conditional relative entropy
-- statement:
--   Let $\rho$ have matching local question copies and be classical on the remote copied question $\widehat Y$. Let $q^{XY}$ be its question law after tracing $\widehat X$, and let $\nu_A$ be an Alice conditional comparison for $\mu$ with finite full divergence. Then
--
--   $$D(\rho^{RXA}\|\nu_A)-D(\rho^{XA}\|\nu_A^{XA})\ge I(\widehat Y:A\mid X)_\rho+D(q^{XY}\|q_X\mu_{Y\mid X}).$$
--
--   Equality holds when both states are diagonal. For a copied-input family the left side is $b_A$; the uniformly quantified alphabets also give the full Bob bound after exchanging the roles of the players.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 21, Lemma 2.26, Eq. (22); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_allocation

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_26
    {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A]
    (μ : Law (X × Y)) (ρ ν : Op (AliceIndex X Y A))
    (hρ : IsState ρ) (hmatch : copyMatching ρ) (hclassical : classicalRemote ρ)
    (hν : IsComparison μ ν) (hf : FiniteD ρ ν) :
    informationRHS μ ρ ≤ charge ρ ν ∧
    (isDiagonal ρ → isDiagonal ν → charge ρ ν = informationRHS μ ρ) := by sorry
end JainCRERepetition.Cubic
