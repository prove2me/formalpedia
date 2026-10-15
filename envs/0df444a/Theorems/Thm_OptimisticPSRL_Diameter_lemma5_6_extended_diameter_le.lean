-- Prove2me | Theorems.Thm_OptimisticPSRL_Diameter_lemma5_6_extended_diameter_le
-- name    : OptimisticPSRL.Diameter.lemma5_6_extended_diameter_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:30.479748+00:00
-- url     : https://prove2.me/theorems/89b33867-f702-4170-8a16-126f7c1fed22
-- title:
--   Lemma 5.6, p. 12 — if every state-action pair has a sample δ-optimistic for every E^s, then D(M̃) ≤ D/(1−δ)
-- statement:
--   Let $\mathcal M$ be a finite MDP with states $\mathcal S$, actions $\mathcal A$, transition probability vectors $P_{s,a}$ and diameter $D=D(\mathcal M)\in[0,\infty]$ (Definition 2: the maximum over ordered pairs of distinct states $s\neq s'$ of the minimum over deterministic stationary policies of the expected number of steps from $s$ to $s'$). For each target state $s$ let $E^{s}\in[0,\infty]^{\mathcal S}$ be the vector of minimum expected times to reach $s$, $E^{s}_{s'}=\min_{\pi}T^{\pi}_{s'\to s}$.
--
--   Let $\psi\ge 0$ and let $Q^{j}_{s,a}$, $j=1,\dots,\psi$, be probability vectors on $\mathcal S$, one family for every state-action pair, and let $\tilde{\mathcal M}$ be the extended MDP in which taking action $a^{j}$ in state $s$ moves according to $Q^{j}_{s,a}$. Let $\delta\in[0,1)$. Suppose that for every target state $s$, every state $s'$ and every action $a$ there is a sample index $j$ with
--   $$Q^{j}_{s',a}\cdot E^{s} \;\le\; P_{s',a}\cdot E^{s}+\delta. \tag{16}$$
--   Then
--   $$D(\tilde{\mathcal M}) \;\le\; \frac{D(\mathcal M)}{1-\delta}.$$
--
--   In the paper this lemma is what makes the sampled extended MDP of each epoch communicating with diameter of the same order as the true one; combined with Lemma 5.7, which shows that (16) holds with $\delta\le 1/2$ with high probability for the posterior samples, it yields $D(\tilde{\mathcal M}^{k})\le 2D$, an ingredient of the regret bound (Theorem 1).
--
--   **Formalization Note.** States, actions and samples are 0-based (`Fin S`, `Fin A`, `Fin ψ`); the extended MDP is `extendedMDP M Q hQ`, with action $a^{j}$ encoded as `finProdFinEquiv (a, j)` in `Fin (A * ψ)`. Diameters are the platform's `mdpDiameterENN` in $[0,\infty]$, $E^{s}$ is `minTravel M s`, the inner products are $\sum_i Q^{j}_{s',a}(i)E^{s}_i$ computed in $[0,\infty]$ (with $0\cdot\infty=0$), and $D/(1-\delta)$ is division in $[0,\infty]$ by the positive number $1-\delta$. The printed (16) uses the letter $s$ both for the target of $E^{s}$ and for the state of $P_{s,a}$, quantified "for every $s,a$"; the proof applies it at the current state $s\neq s_2$ with target $s_2$, so the target is quantified separately here (for every target, state and action). No communicating assumption is made: if $D(\mathcal M)=\infty$ the bound holds trivially, so the statement generalizes the paper's. The sample vectors are arbitrary probability vectors; no positivity of their entries and no distributional assumption is made.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 12, Lemma 5.6 (display (16)); proof pp. 12–13

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_OptimisticPSRL_Diameter_Setting
open BanditAlgorithm NNReal ENNReal

namespace OptimisticPSRL.Diameter
theorem lemma5_6_extended_diameter_le {S A ψ : ℕ} (M : FiniteMDP S A)
    (Q : Fin S → Fin A → Fin ψ → Fin S → ℝ≥0) (hQ : ∀ s a j, ∑ i, Q s a j i = 1)
    (δ : ℝ≥0) (hδ : δ < 1)
    (h16 : ∀ tgt s : Fin S, ∀ a : Fin A, ∃ j : Fin ψ,
      ∑ i, (Q s a j i : ℝ≥0∞) * minTravel M tgt i ≤
        ∑ i, (M.P s a i : ℝ≥0∞) * minTravel M tgt i + δ) :
    mdpDiameterENN (extendedMDP M Q hQ) ≤ mdpDiameterENN M / ((1 - δ : ℝ≥0) : ℝ≥0∞) := by sorry
end OptimisticPSRL.Diameter
