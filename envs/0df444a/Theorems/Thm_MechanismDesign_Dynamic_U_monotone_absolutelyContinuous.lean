-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_U_monotone_absolutelyContinuous
-- name    : MechanismDesign.Dynamic.U_monotone_absolutelyContinuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:54:10.459806+00:00
-- url     : https://prove2.me/theorems/17aac18d-6fbf-475b-bda2-c49751f73d9f
-- title:
--   Lemma 11.1 -- $U(\tau)$ is increasing and absolutely continuous
-- statement:
--   If an admissible direct mechanism in the sequential screening model is incentive-compatible, then the ex ante utility
--   $$U(\tau)=\int_{\underline\theta}^{\bar\theta}\bigl[\hat\theta q(\tau,\hat\theta)-t(\tau,\hat\theta)\bigr]f(\hat\theta\mid\tau)\,d\hat\theta$$
--   is increasing and absolutely continuous on $[\underline\tau,\bar\tau]$.
--
--   Absolute continuity is what allows $U$ to be recovered from its derivative, the step to the envelope formula of Proposition 11.4.
--
--   **Formalization Note** "Increasing" is weak monotonicity (Börgers' convention); absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval`.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.211, Lemma 11.1

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

namespace MechanismDesign.Dynamic

/-- **Lemma 11.1**, p.211. If an (admissible) direct mechanism is incentive-compatible, then
`U(τ)` is increasing and absolutely continuous on `[τ̲, τ̄]`. -/
theorem U_monotone_absolutelyContinuous {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    MonotoneOn (m.U E) (Set.Icc τlo τhi) ∧ AbsolutelyContinuousOnInterval (m.U E) τlo τhi := by sorry

end MechanismDesign.Dynamic
