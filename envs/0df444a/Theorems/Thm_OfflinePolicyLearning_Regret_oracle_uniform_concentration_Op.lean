-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_oracle_uniform_concentration_Op
-- name    : OfflinePolicyLearning.Regret.oracle_uniform_concentration_Op
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:57.473734+00:00
-- url     : https://prove2.me/theorems/e683f016-3970-41ab-9dc5-a2a855f74839
-- title:
--   Lemma 2, p. 19, as used in (18), p. 22 (pinned: O_p(n^{−1/2}) form) — √n · sup_{π₁,π₂∈Π} |Δ̃(π₁,π₂) − Δ(π₁,π₂)| = O_p(1)
-- statement:
--   Work in the potential-outcome model of the mission. Assume overlap $e_a(x)\ge\eta>0$ and bounded rewards $|Y(a)|\le B$ (Assumption 1; unconfoundedness is built into the model); that $\Pi$ is nonempty, its policies measurable and the class permissible (for every $m$ and action pattern $s$, the set of point sequences on which some $\pi\in\Pi$ realizes $s$ is measurable); and Assumption 3: for all $0<\varepsilon<1$, $N_H(\varepsilon,\Pi)$ is finite and
--   $$N_H(\varepsilon,\Pi)\le C\exp\big(D(1/\varepsilon)^{\omega}\big)$$
--   for constants $C,D>0$, $0<\omega<1/2$. Then
--   $$\sup_{\pi_1,\pi_2\in\Pi}\big|\tilde\Delta(\pi_1,\pi_2)-\Delta(\pi_1,\pi_2)\big|=O_p\Big(\frac1{\sqrt n}\Big):$$
--   for every $\varepsilon>0$ there are $M>0$ and $N$ such that for all $n\ge N$,
--   $$\mathbb P\Big(\exists\,\pi_1,\pi_2\in\Pi:\ |\tilde\Delta(\pi_1,\pi_2)-\Delta(\pi_1,\pi_2)|>M/\sqrt n\Big)\le\varepsilon.$$
--
--   This is the uniform concentration of the oracle value differences around the true ones, the second ingredient of the regret bound.
--
--   **Formalization Note** This replaces the printed Lemma 2 (explicit constant $54.4\sqrt2\kappa(\Pi)+435.2$ and an $o(1/\sqrt n)$ remainder) and the $O_p((\kappa(\Pi)+1)\sqrt{V_*/n})$ of (18). The explicit constant rests on Theorem 1, whose $\sqrt{V_*}$ scaling fails in general and whose proof uses the false Lemma 1(2); and $O_p((\kappa(\Pi)+1)\sqrt{V_*/n})$ is false when $V_*=0$ (a class of point-switching policies with $V_*=0$ and $\tilde\Delta-\Delta=1/n$ surely). Assumption 3's finiteness of $N_H$ is written out, because the bound is stated on the natural-number value of the extended covering number and that value of $\infty$ would be the junk value $0$. $O_p$ is read for each $n$ separately (the samples of different sizes live on different spaces). Permissibility is added (see Lemma 3).
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 19, Lemma 2 (11); p. 22, display (18), second-to-last equality; O_p of Definition 8 item 1, p. 21; Assumption 3, p. 14

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem oracle_uniform_concentration_Op {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (Pol : Set (X → Fin d)) (hPol : Pol.Nonempty) (hPmeas : ∀ π ∈ Pol, Measurable π)
    (hperm : ∀ (m : ℕ) (s : Fin m → Fin d),
      MeasurableSet {x : Fin m → X | ∃ π ∈ Pol, ∀ i, π (x i) = s i})
    (Cc Dc ω : ℝ) (hCc : 0 < Cc) (hDc : 0 < Dc) (hω : 0 < ω) (hω' : ω < 1 / 2)
    (h3 : ∀ ε : ℝ, 0 < ε → ε < 1 → hammingCoverNum ε Pol ≠ ⊤ ∧
      ((hammingCoverNum ε Pol).toNat : ℝ) ≤ Cc * Real.exp (Dc * (1 / ε) ^ ω)) :
    ∀ ε : ℝ, 0 < ε → ∃ Mc : ℝ, 0 < Mc ∧ ∃ N : ℕ, ∀ n ≥ N,
      M.sample n {D | ∃ πa ∈ Pol, ∃ πb ∈ Pol,
        Mc / Real.sqrt n < |M.Δtilde D πa πb - M.Δ πa πb|} ≤ ENNReal.ofReal ε := by sorry
end OfflinePolicyLearning.Regret
