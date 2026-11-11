-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_14
-- name    : MultiOmniRate.Lipschitz.lemma_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:24:37.451885+00:00
-- url     : https://prove2.me/theorems/cdcac910-1bdb-40e6-89c1-ee1f7f49fafa
-- title:
--   Lemma 3.14 — a decision learner with $\mathrm{Reg}_{\mathrm{dec}}(n,r)=C_Knr+C_K\sqrt n\,f_K(r)$
-- statement:
--   Fix $K\ge2$. There is $C_K$, depending only on $K$, such that for every $0<r\le1/2$ and $n\ge1$ there is an online learner satisfying the decision guarantee of Definition 3.6 (continuous tests $w_t:\Delta_K\to[-5,5]^K$ from past feedback, and $\sup_{\ell\in\mathcal L_{\mathrm{All}}}|\sum_t\langle w_{\ell,r}(q_t),e_{y_t}-q_t\rangle|\le\sum_t\langle w_t(q_t),e_{y_t}-q_t\rangle+\mathrm{Reg}_{\mathrm{dec}}(n,r)$ for every sequence) with
--   $$\mathrm{Reg}_{\mathrm{dec}}(n,r)=C_Knr+C_K\sqrt n\,f_K(r),\qquad f_K(r)=\begin{cases}\sqrt{\log(2/r)},&K=2,\\ r^{-1/4},&K=3,\\ r^{-1/2}\log(2/r),&K=4,\\ r^{-(K-3)/2},&K\ge5.\end{cases}\quad(3.4)$$
--
--   This regret produces the $\varepsilon^{-\max\{K-1,(K+2)/2\}}$ term of the main theorem.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: rounds $t=1,\dots,n$ → rounds $t=0,\dots,n-1$ (`Finset.range n` or `Fin n`); reason: index shift only
--   - encoding: an online learner of Definition 3.6(1) "using only feedback from preceding rounds and its own randomization", guarantee for every adaptive sequence → a deterministic `DecLearner` whose round-$t$ test is a function of the history of rounds $<t$; the guarantee for every sequence $(q_t,y_t)$; reason: the decision guarantee has no expectation, so a randomized learner must meet it for every realization of its randomness; against a deterministic learner an adaptive sequence is a fixed sequence
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 35, Lemma 3.14 and (3.4)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_14.{u} : ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : ℝ), 0 < r → r ≤ 1 / 2 →
      ∃ Lr : DecLearner K,
        DecLearner.Guarantee.{u} Lr n r (C * n * r + C * Real.sqrt n * fK K r) := by sorry

end MultiOmniRate.Lipschitz
