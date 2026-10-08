-- Prove2me | Theorems.Thm_LeiBR_Rand_remark_6
-- name    : LeiBR.Rand.remark_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:44.887444+00:00
-- url     : https://prove2.me/theorems/3f836b9e-4961-4be7-b563-6eb1887db361
-- title:
--   Remark 6 — $u_k \le p_{\max}^{1/2}\,\mathbb E\|x_k - x^*\|_P \le (Np_{\max})^{1/2}(\tilde C + \tilde D)\tilde q^k$
-- statement:
--   Under the hypotheses of Lemma 5, let $u_k = \mathbb E\big[\big(\sum_{i=1}^N \|x_{i,k} - x_i^*\|^2\big)^{1/2}\big]$ and $p_{\max} = \max_i p_i$. Then
--   $$u_k \le p_{\max}^{1/2}\,\mathbb E\big[\|x_k - x^*\|_P\big] \le (Np_{\max})^{1/2}\,(\tilde C + \tilde D)\,\tilde q^k \qquad \forall k \ge 0.$$
--
--   It transfers the rate of Lemma 5 from the weighted norm to the unweighted error $u_k$ that defines an $\epsilon$-NE$_2$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 15, Remark 6

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- Remark 6, p. 15. Under the hypotheses of Lemma 5, with `u_k = E‖(‖x_{i,k} − x*_i‖)_i‖`,
`u_k ≤ p_max^{1/2} E‖x_k − x*‖_P ≤ (N p_max)^{1/2} (C̃ + D̃) q̃^k`. -/
theorem remark_6 {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (w : ∀ i, ℕ → Ω → LeiBR.Sync.Strat n i) (x0 : LeiBR.Sync.Profile n)
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (C : ℝ) (hC : ∀ i, ‖x0 i - xstar i‖ ≤ C)
    (hrun : IsAlg2Run G xhat P F p χ w (fun i k ω => η ^ (beta χ i k ω + 1)) x0 x)
    (q : ℝ) (hq : ctil p (contrFactor G mu) η < q) (hq1 : q < 1) (k : ℕ) :
    ∫ ω, blockNorm (x k ω - xstar) ∂P ≤ Real.sqrt (pmax p) * ∫ ω, wnorm p (x k ω - xstar) ∂P ∧
    Real.sqrt (pmax p) * ∫ ω, wnorm p (x k ω - xstar) ∂P ≤
      Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) * q ^ k := by sorry

end LeiBR.Rand
