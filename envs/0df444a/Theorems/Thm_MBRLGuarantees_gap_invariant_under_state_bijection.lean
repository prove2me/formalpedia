-- Prove2me | Theorems.Thm_MBRLGuarantees_gap_invariant_under_state_bijection
-- name    : MBRLGuarantees.gap_invariant_under_state_bijection
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:29:43.391064+00:00
-- url     : https://prove2.me/theorems/c8518999-3dd3-4888-8438-99b37be79976
-- title:
--   Proposition 4.4 (invariance): $G$ is invariant under a one-to-one change of state representation
-- statement:
--   In the setting of Lemma C.1, let $\widehat M$ and $M^\star$ be deterministic measurable models and $\pi$ a deterministic measurable policy, and transform $\widehat M$, $M^\star$, $\pi$ and $R$ by $\mathcal T$. Then the one-step discrepancy is unchanged: for all $s\in\mathcal S$ and actions $a$,
--
--   $$G^{\mathcal T}(\mathcal Ts,a)=V^{\pi^{\mathcal T},\widehat M^{\mathcal T}}\big(\widehat M^{\mathcal T}(\mathcal Ts,a)\big)-V^{\pi^{\mathcal T},\widehat M^{\mathcal T}}\big(M^{\star,\mathcal T}(\mathcal Ts,a)\big)=G(s,a),$$
--
--   where $G(s,a)=V^{\pi,\widehat M}(\widehat M(s,a))-V^{\pi,\widehat M}(M^\star(s,a))$ and the transformed values use $R^{\mathcal T}$.
--
--   Unlike a norm on the states, the discrepancy bound $D^G$ therefore does not depend on the choice of state representation.
--
--   **Formalization Note** Eq. (C.1) writes $G^{\mathcal T}$ with an absolute value; the statement is the equality without absolute values, which implies it.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 4.2, Proposition 4.4 (last sentence), p. 7; eq. (C.1) in Appendix C.1, p. 17

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem gap_invariant_under_state_bijection {S S' A : Type*} [MeasurableSpace S]
    [MeasurableSpace S'] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (T : S ≃ᵐ S') (mhat mstar : S × A → S) (hmhat : Measurable mhat) (hmstar : Measurable mstar)
    (p : S → A) (hp : Measurable p)
    (mhatT mstarT : S' × A → S') (hmhatT : Measurable mhatT) (hmstarT : Measurable mstarT)
    (hmhatT_eq : ∀ x, mhatT x = T (mhat (T.symm x.1, x.2)))
    (hmstarT_eq : ∀ x, mstarT x = T (mstar (T.symm x.1, x.2)))
    (pT : S' → A) (hpT : Measurable pT) (hpT_eq : ∀ x, pT x = p (T.symm x)) (s : S) (a : A) :
    gapFn γ (fun x : S' × A => R (T.symm x.1, x.2)) (Kernel.deterministic pT hpT)
        (Kernel.deterministic mhatT hmhatT) (Kernel.deterministic mstarT hmstarT) (T s) a =
      gapFn γ R (Kernel.deterministic p hp) (Kernel.deterministic mhat hmhat)
        (Kernel.deterministic mstar hmstar) s a := by sorry

end MBRLGuarantees
