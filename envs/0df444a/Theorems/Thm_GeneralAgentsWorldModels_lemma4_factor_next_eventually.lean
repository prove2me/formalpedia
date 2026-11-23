-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma4_factor_next_eventually
-- name    : GeneralAgentsWorldModels.lemma4_factor_next_eventually
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:37:05.131923+00:00
-- url     : https://prove2.me/theorems/5f628f71-feca-4a0c-890f-1766aea09b8c
-- title:
--   Lemma 4 (as proved): factoring a Next sub-goal followed by an Eventually sub-goal
-- statement:
--   Let the environment satisfy Assumption 1, let $\psi=\langle\varphi_1,\varphi_2,\varphi_3,\dots,\varphi_L\rangle$ with $\varphi_1=\medcirc([S\in g_1])$ for a set of states $g_1\subseteq S$ and $\varphi_2=\Diamond([S=s_g,A=a_g])$, and let $\mu$ be a deterministic stationary Markov policy such that from every state $x\in g_1$, $\mu$ eventually reaches $s_g$ and takes $a_g$ there with probability one. Then
--
--   $$P(\tau\models\psi\mid s_0,\mu)=P(S_1\in g_1\mid s_0,\mu)\,P\big(\tau\models\langle\varphi_3,\dots,\varphi_L\rangle\mid s_g,\mu\big),$$
--
--   where $P(S_1\in g_1\mid s_0,\mu)=\sum_{x\in g_1}P_{s_0x}(\mu(s_0))$.
--
--   **Formalization Note** The printed Lemma 4 assumes only that $\mu$ is deterministic and Markovian. Its proof applies Lemma 3 from each $s_1\in g_1$ (eq. (20)), which needs the reachability hypothesis added here; without it the printed identity fails (a policy that never reaches $s_g$ gives $0$ on the left and $P(S_1\in g_1\mid s_0,\mu)>0$ on the right when $L=2$).
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 4, eqs. (15)-(21), p. 15 (uses Lemma 3 at eq. (20))

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma4_factor_next_eventually {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (μ : S → A) (g₁ : Set S) (sg : S) (ag : A)
    (rest : SeqGoal S A) (s₀ : S)
    (hreach : ∀ x ∈ g₁, succProb M [[evVisit sg ag]] (fun _ y => μ y) x = 1) :
    succProb M [nextIn g₁ :: evVisit sg ag :: rest] (fun _ y => μ y) s₀ =
      (∑ x : S, g₁.indicator (fun y => M.P s₀ (μ s₀) y) x) *
        succProb M [rest] (fun _ y => μ y) sg := by sorry

end GeneralAgentsWorldModels
