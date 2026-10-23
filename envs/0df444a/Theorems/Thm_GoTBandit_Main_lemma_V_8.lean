-- Prove2me | Theorems.Thm_GoTBandit_Main_lemma_V_8
-- name    : GoTBandit.Main.lemma_V_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:26.717481+00:00
-- url     : https://prove2.me/theorems/68064a0f-b0a1-435b-a43f-5903d592343a
-- title:
--   Lemma V.8, Eq. (33), pp. 10–11 — the GoT phases of the last ⌊k/2⌋ + 1 epochs fail with probability ≤ (C0 e^{−…(k/2)^δ})^k
-- statement:
--   Fix $N\le M$, $M\ge2$, $c_2\ge1$, $\delta>0$, $0<\varepsilon<1$, $c>0$ and a bound $K$. There is a constant $C_0$ such that the following holds for all sequences, indexed by epochs $i$, of positive utilities $U^i$ with unique optimal profiles $a^{i*}$, stationary distributions $\pi^i$ of the GoT chains $P^\varepsilon$ of $U^i$, and initial laws $\phi^i$ vanishing where $\pi^i$ does with $\|\phi^i\|_{\pi^i}\le K$.
--
--   Consider independent runs, one per epoch $i$ of the window $k-\lfloor k/2\rfloor\le i\le k$: run $i$ is the chain of $U^i$ started from $\phi^i$ for $\lceil c_2i^\delta\rceil$ turns. Let $z^{i*}=[a^{i*},C^N]$,
--
--   $$
--   F_k(z^*)=\sum_{i=k-\lfloor k/2\rfloor}^k\sum_{t\in\mathcal G_i}I(z(t)=z^{i*}),\qquad \pi_{z^*}=\min_{k-\lfloor k/2\rfloor\le i\le k}\pi^i_{z^{i*}},\qquad T_m(\tfrac18)=\max_{k-\lfloor k/2\rfloor\le i\le k}T_{m,i}(\tfrac18).
--   $$
--
--   For every $0<\eta<\tfrac12$ there is $k_0$ such that for all $k\ge k_0$: if $\pi_{z^*}>\frac1{2(1-\eta)}$, then
--
--   $$
--   P_{c,k}=\mathbb P\Big(F_k(z^*)\le\frac12\sum_{i=k-\lfloor k/2\rfloor}^kc_2i^\delta\Big)\le\Big(C_0e^{-\frac{c_2\eta^2}{144T_m(1/8)}\left(\pi_{z^*}-\frac1{2(1-\eta)}\right)(k/2)^\delta}\Big)^k.
--   $$
--
--   This bounds the probability that the majority vote of the exploitation phase of epoch $k$ misses the optimal profile; it is the second term of the per-epoch regret bound (11).
--
--   **Formalization Note** The statement is the stand-alone form the proof uses: the GoT runs of the window are independent given their starting states (p. 11), here with deterministic utilities and starting laws. $C_0$ is independent of $k$, $\pi_{z^*}$ and $\eta$, as printed, and also of the utilities and starting laws; it may depend on the bound $K$, which plays the role of the paper's bound on $\mathbb E\{A_i\}$. The starting laws vanish where the stationary distributions do (see Lemma V.7). $T_{m,i}(1/8)$ is the worst-start total-variation mixing time. Here $\eta$ is the slack parameter, not the collision indicator.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, pp. 10–11, Lemma V.8, Eqs. (32)–(33)

import Mathlib
import Definitions.Def_GoTBandit_Main_GoTChain

namespace GoTBandit.Main

/-- Lemma V.8, pp. 10–11, Eq. (33), for independent GoT runs of the last `⌊k/2⌋ + 1` epochs
(run `i` has utilities `U i`, `⌈c2 i^δ⌉` turns, start law `ϕ i` with `‖ϕ i‖_π ≤ K`): with
`π_{z*}` the window minimum of the optimal states' stationary masses and `T_m(1/8)` the window
maximum of the mixing times, if `π_{z*} > 1/(2(1 − η))` with `0 < η < 1/2` then for large `k`
the total number of visits to the optimal states is at most `½ ∑_i c2 i^δ` with probability at
most `(C0 e^{−(c2η²/(144 T_m(1/8)))(π_{z*} − 1/(2(1−η)))(k/2)^δ})^k`. -/
theorem lemma_V_8 {N M : ℕ} (hNM : N ≤ M) (hM : 2 ≤ M) (c2 : ℕ) (hc2 : 0 < c2) (δ : ℝ)
    (hδ : 0 < δ) (ε c : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (K : ℝ) :
    ∃ C0 : ℝ, ∀ (U : ℕ → Fin N → Fin M → ℝ) (aStar : ℕ → Fin N → Fin M)
      (π ϕ : ℕ → Z N M → ℝ),
      (∀ i n j, 0 < U i n j) →
      (∀ i, IsOptimal (U i) (aStar i) ∧ ∀ a, IsOptimal (U i) a → a = aStar i) →
      (∀ i, MarkovMixing.IsStationary (gotMatrix (U i) ε c) (π i)) →
      (∀ i, MarkovMixing.IsDist (ϕ i)) → (∀ i z, π i z = 0 → ϕ i z = 0) →
      (∀ i, normPi (ϕ i) (π i) ≤ K) →
      ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        1 / (2 * (1 - η)) < windowMin (fun i => π i (zStar (aStar i))) k →
        windowProb (fun i => gotMatrix (U i) ε c) ϕ (fun i => gotLen c2 δ i) (window k)
            {p | (∑ i : window k, (visits (zStar (aStar i)) (p i) : ℝ)) ≤
              1 / 2 * ∑ i ∈ window k, (c2 : ℝ) * (i : ℝ) ^ δ} ≤
          (C0 * Real.exp (-((c2 : ℝ) * η ^ 2 /
              (144 * windowMax (fun i =>
                (MarkovMixing.mixingTime (gotMatrix (U i) ε c) (π i) (1 / 8) : ℝ)) k)) *
            (windowMin (fun i => π i (zStar (aStar i))) k - 1 / (2 * (1 - η))) *
            ((k : ℝ) / 2) ^ δ)) ^ k := by sorry

end GoTBandit.Main
