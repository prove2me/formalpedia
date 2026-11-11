-- Prove2me | Theorems.Thm_JainCRERepetition_Cubic_lemma_2_20
-- name    : JainCRERepetition.Cubic.lemma_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:47.891771+00:00
-- url     : https://prove2.me/theorems/13d283ca-033f-4cb4-ad82-02170d11d32d
-- title:
--   Lemma 2.20 — conditional relative-entropy decomposition
-- statement:
--   Let $q^{XY}$ and $r_X$ be probability laws, $\mu(y\mid x)$ a conditional law, and $\rho_{xy},\sigma_x$ density operators on $A$. Form the classical–quantum states with blocks $q(x,y)\rho_{xy}$ and $r_X(x)\mu(y\mid x)\sigma_x$, respectively. If their full divergence is finite, then
--
--   $$D(\rho^{XYA}\|\nu^{XYA})-D(\rho^{XA}\|\nu^{XA})=I(Y:A\mid X)_\rho+D(q^{XY}\|q_X\mu_{Y\mid X}).$$
--
--   The comparison marginal $r_X$ need not equal $q_X$. This separates workspace variation from a change in the conditional question law.
--
--   Differences from the source:
--   - encoding: finite complex systems with support-aware binary relative entropy → complex matrices on finite bases; FiniteD guards real divergence differences; reason: kernel containment is the finite-divergence condition; no infinite divergence is converted to zero
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), p. 17, Lemma 2.20; pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_allocation

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

theorem lemma_2_20
    {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A]
    (q : Law (X × Y)) (r : Law X) (μ : X → Law Y)
    (ρ : X → Y → Op A) (σ : X → Op A)
    (hρ : ∀ x y, IsState (ρ x y)) (hσ : ∀ x, IsState (σ x))
    (hf : FiniteD (cqXY q.p ρ) (cqXY (fun xy => r.p xy.1 * (μ xy.1).p xy.2)
      (fun x _ => σ x))) :
    d (cqXY q.p ρ) (cqXY (fun xy => r.p xy.1 * (μ xy.1).p xy.2) (fun x _ => σ x)) -
      d (cqXA q.p ρ) (cq r.p σ) = conditionalInfo q.p ρ +
        classicald q.p (fun xy => marginalX q.p xy.1 * (μ xy.1).p xy.2) := by sorry
end JainCRERepetition.Cubic
