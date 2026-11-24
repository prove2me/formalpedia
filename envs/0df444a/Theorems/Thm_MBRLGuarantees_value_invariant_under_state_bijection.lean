-- Prove2me | Theorems.Thm_MBRLGuarantees_value_invariant_under_state_bijection
-- name    : MBRLGuarantees.value_invariant_under_state_bijection
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:27:41.928227+00:00
-- url     : https://prove2.me/theorems/e4a5efd2-1603-45d4-97e5-f7643cdfc7cb
-- title:
--   Lemma C.1: values are invariant under a one-to-one change of state representation
-- statement:
--   Let $\gamma\in[0,1)$ and let $R$ be bounded and measurable. Let $\mathcal T:\mathcal S\to\mathcal S'$ be a one-to-one correspondence, measurable in both directions, let $M$ be a deterministic measurable model and $\pi$ a deterministic measurable policy, and define the transformed model, reward and policy
--
--   $$M^{\mathcal T}(s,a)=\mathcal T M(\mathcal T^{-1}s,a),\qquad R^{\mathcal T}(s,a)=R(\mathcal T^{-1}s,a),\qquad\pi^{\mathcal T}(s)=\pi(\mathcal T^{-1}s).$$
--
--   Then for every $s\in\mathcal S$,
--
--   $$V^{\pi^{\mathcal T},M^{\mathcal T}}(\mathcal Ts)=V^{\pi,M}(s),$$
--
--   where the left side is computed with the reward $R^{\mathcal T}$.
--
--   So a change of state representation is not identifiable from rewards alone.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Appendix C.1, Lemma C.1, p. 17

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem value_invariant_under_state_bijection {S S' A : Type*} [MeasurableSpace S]
    [MeasurableSpace S'] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (T : S ≃ᵐ S') (m : S × A → S) (hm : Measurable m) (p : S → A) (hp : Measurable p)
    (mT : S' × A → S') (hmT : Measurable mT) (hmT_eq : ∀ x, mT x = T (m (T.symm x.1, x.2)))
    (pT : S' → A) (hpT : Measurable pT) (hpT_eq : ∀ x, pT x = p (T.symm x)) (s : S) :
    stateValue γ (fun x : S' × A => R (T.symm x.1, x.2)) (Kernel.deterministic pT hpT)
        (Kernel.deterministic mT hmT) (T s) =
      stateValue γ R (Kernel.deterministic p hp) (Kernel.deterministic m hm) s := by sorry

end MBRLGuarantees
