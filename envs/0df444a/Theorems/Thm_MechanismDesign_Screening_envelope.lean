-- Prove2me | Theorems.Thm_MechanismDesign_Screening_envelope
-- name    : MechanismDesign.Screening.envelope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T22:43:58.500309+00:00
-- url     : https://prove2.me/theorems/815a7a3f-4b9a-4819-90a5-6a8c9deed40d
-- title:
--   Lemma 2.2 -- envelope: $u$ is increasing and convex with $u'(\theta)=q(\theta)$
-- statement:
--   Let $(q,t)$ be an incentive-compatible direct mechanism on $[\underline\theta,\bar\theta]$, $0\le\underline\theta<\bar\theta$, and let $u(\theta)=\theta q(\theta)-t(\theta)$. Then:
--
--   1. $u$ is increasing on $[\underline\theta,\bar\theta]$;
--   2. $u$ is convex on $[\underline\theta,\bar\theta]$;
--   3. $u$ is differentiable at all but at most countably many points of $(\underline\theta,\bar\theta)$;
--   4. at every $\theta\in(\underline\theta,\bar\theta)$ at which $u$ is differentiable,
--   $$u'(\theta)=q(\theta).$$
--
--   This is the envelope theorem in the screening model, and the step from which payoff equivalence (Lemma 2.3) follows.
--
--   **Formalization Note** The derivative identity is stated at interior points. At an endpoint the one-sided derivative of $u$ equals the one-sided limit of $q$, which can differ from $q(\underline\theta)$ or $q(\bar\theta)$ (e.g. $q=0$ at $\underline\theta$ and $q=1$ to its right), so the book's "for all $\theta$ at which $u$ is differentiable" is read on the open interval.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.11, Lemma 2.2

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

namespace MechanismDesign.Screening

/-- **Lemma 2.2**, p.11. If a direct mechanism is incentive-compatible, then `u` is increasing and
convex on `[θ̲, θ̄]`, hence differentiable at all but countably many points of `(θ̲, θ̄)`, and
`u′(θ) = q(θ)` at every interior point `θ` at which `u` is differentiable. -/
theorem envelope {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.u (Set.Icc θlo θhi) ∧ ConvexOn ℝ (Set.Icc θlo θhi) m.u ∧
      {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ m.u θ}.Countable ∧
      ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ m.u θ → deriv m.u θ = m.q θ := by sorry

end MechanismDesign.Screening
