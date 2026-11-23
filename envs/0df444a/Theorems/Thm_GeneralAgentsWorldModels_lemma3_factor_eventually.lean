-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma3_factor_eventually
-- name    : GeneralAgentsWorldModels.lemma3_factor_eventually
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:36:34.673796+00:00
-- url     : https://prove2.me/theorems/b0475c65-94c4-45ca-a939-796fc990a46b
-- title:
--   Lemma 3: factoring an Eventually sub-goal
-- statement:
--   Let the environment satisfy Assumption 1, let $\psi=\langle\varphi_1,\varphi_2,\dots,\varphi_L\rangle$ with $\varphi_1=\Diamond([S=s_g,A=a_g])$, and let $\mu$ be a deterministic stationary Markov policy that, from $S_0=s_0$, eventually reaches $s_g$ and takes $a_g$ there with probability one. Then
--
--   $$P\big(\tau\models\langle\varphi_1,\varphi_2,\dots,\varphi_L\rangle\mid\mu,s_0\big)=P\big(\tau\models\langle\varphi_2,\dots,\varphi_L\rangle\mid\mu,s_g\big).$$
--
--   For $L=1$ the right-hand side is the probability of the empty sequential goal, which is $1$.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 3, eqs. (8)-(14), pp. 14-15

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma3_factor_eventually {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (μ : S → A) (sg : S) (ag : A)
    (rest : SeqGoal S A) (s₀ : S)
    (hreach : succProb M [[evVisit sg ag]] (fun _ x => μ x) s₀ = 1) :
    succProb M [evVisit sg ag :: rest] (fun _ x => μ x) s₀ =
      succProb M [rest] (fun _ x => μ x) sg := by sorry

end GeneralAgentsWorldModels
