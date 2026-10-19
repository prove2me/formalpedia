-- Prove2me | Theorems.Thm_OffPolicyDRL_CrossFit_lemma_1
-- name    : OffPolicyDRL.CrossFit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:40.579858+00:00
-- url     : https://prove2.me/theorems/cf3ea29b-00db-476d-b96a-475f0dbdffd7
-- title:
--   Lemma 1 (forward direction) — the stationary density ratio w satisfies L(w, f) = 0 for every bounded measurable f
-- statement:
--   Work in the off-policy evaluation model under its standing assumptions (Markov kernels, rewards in $[0,R_{\max}]$, $0\le\gamma<1$, overlap). Let $w$ be the stationary density ratio $p^{(\infty)}_{\pi_e,\gamma}/p^{(0)}_{\pi_b}$, $\eta=\pi_e/\pi_b$, and $(s,a,r,s')\sim p_{\pi_b}$. Then for every bounded measurable $f:S\to\mathbb R$,
--   $$L(w,f)=\mathbb E\big[\gamma w(s)\eta(s,a)f(s')-w(s)f(s)\big]+(1-\gamma)\,\mathbb E_{p^{(0)}_{\pi_e}}[f(s)]=0.$$
--
--   This identity characterizes $w$ through the behavior data alone. It is what makes the estimating function $\psi$ unbiased when $w'=w$, whatever $q'$ is (Eqs. (6)–(8)).
--
--   **Formalization Note** Only the forward direction is stated. The converse in the paper (uniqueness under an integral-equation condition) is not used by Theorem 6. Test functions are bounded measurable, which covers every use in the paper ($f=v'$ for bounded $q'$).
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Lemma 1 (Eq. (11)), p. 32; proof pp. 68–69

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

theorem lemma_1 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace.CountablyGenerated A] (M : Model S A) (hM : M.Standing)
    (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ s, |f s| ≤ C) :
    M.Lfun M.w f = 0 := by sorry

end OffPolicyDRL.CrossFit
