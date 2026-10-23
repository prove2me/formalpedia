-- Prove2me | Theorems.Thm_KellyStochasticNetworks_RandomAccessCapacity_gibbs_stationary
-- name    : KellyStochasticNetworks.RandomAccessCapacity.gibbs_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:32.374768+00:00
-- url     : https://prove2.me/theorems/025e7a96-9656-4536-acc5-343850b4da12
-- title:
--   Equation (5.8) — stationary law of distributed random access
-- statement:
--   Let $G$ be a finite simple interference graph with station set $R$, and let $S\subseteq\{0,1\}^R$ comprise all independent activity vectors. Fix any finite real vector $\theta$. Consider the continuous-time Markov chain that changes $n_r=1$ to $0$ at rate $1$ and changes $n_r=0$ to $1$ at rate $\exp(\theta_r)$ when the new vector belongs to $S$, with no other jumps. Let $Q$ be its generator and $P(t)=\exp(tQ)$ its transition matrix. Then
--
--   $$\pi_\theta(n)=\frac{\exp(\sum_r n_r\theta_r)}{\sum_{m\in S}\exp(\sum_r m_r\theta_r)}$$
--
--   is a probability distribution and is stationary:
--
--   $$\pi_\theta(n)\ge0,\qquad\sum_{n\in S}\pi_\theta(n)=1,\qquad
--   \sum_{n\in S}\pi_\theta(n)P(t)_{nm}=\pi_\theta(m)\quad(t\ge0,\ m\in S).$$
--
--   This identifies the equilibrium service marginals of the actual exclusion dynamics.
--
--   **Formalization Note** The generator has diagonal entries equal to minus its outgoing rates. Stationarity is invariance under every nonnegative-time transition matrix, rather than only a balance equation. The zero-station graph has the single empty state with stationary mass one.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 126 (PDF p. 134), Eq. (5.8), with dynamics on printed p. 125. DOI: 10.1017/cbo9781139565363.

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Network

namespace KellyStochasticNetworks.RandomAccessCapacity

theorem gibbs_stationary {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) :
    let S := {n : Fin d → Fin 2 // ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0}
    let w : S → ℝ := fun n => Real.exp (∑ r, (n.val r : ℝ) * θ r)
    let π : S → ℝ := fun n => w n / ∑ m : S, w m
    let q : S → S → ℝ := fun n m =>
      ∑ r, if (∀ i, i ≠ r → m.val i = n.val i) ∧ m.val r ≠ n.val r
        then (if n.val r = 0 then Real.exp (θ r) else 1) else 0
    let Q : Matrix S S ℝ := fun n m =>
      if n = m then -(∑ k : S, q n k) else q n m
    (∀ n, 0 ≤ π n) ∧ (∑ n : S, π n) = 1 ∧
      ∀ t : ℝ, 0 ≤ t → ∀ m : S,
        (∑ n : S, π n * NormedSpace.exp (t • Q) n m) = π m := by sorry

end KellyStochasticNetworks.RandomAccessCapacity
