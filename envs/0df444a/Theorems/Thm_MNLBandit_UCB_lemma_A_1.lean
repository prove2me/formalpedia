-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_A_1
-- name    : MNLBandit.UCB.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:52:40.110311+00:00
-- url     : https://prove2.me/theorems/58e0abcf-fad0-451f-8e45-f4c5949b6faf
-- title:
--   Lemma A.1, p. 32 — the MGF of an epoch's purchase count of i is 1/(1 − vᵢ(e^θ − 1))
-- statement:
--   Let $v_1,\dots,v_N\ge 0$ be MNL parameters (with $v_0=1$), let $S$ be an assortment offered repeatedly until the first no-purchase, and let $\hat v_i$ be the number of purchases of a product $i\in S$ in this epoch. For every real $\theta$ with $v_i(e^\theta-1)<1$,
--   $$
--   \mathbb E\big[e^{\theta\hat v_i}\big]=\frac{1}{1-v_i(e^\theta-1)}.
--   $$
--   In particular the moment generating function of $\hat v_i$ depends only on $v_i$ and not on the other products of $S$. This is the starting point of the paper's argument that the per-epoch estimates of $v_i$ are i.i.d. even though the offered assortments are chosen adaptively.
--
--   **Formalization Note.** The paper conditions on $S_\ell$; here $S$ is fixed and the epoch is modelled by the i.i.d. law `epochLaw v S`. The expectation is a lower Lebesgue integral of nonnegative values, so it is a genuine (possibly infinite) value. The paper prints $\theta\le\log\frac{1+v_i}{v_i}$; at the endpoint the right-hand side is $1/0$ and the left-hand side is $+\infty$, and the proof's (A.3) uses $\theta<\log\frac{1+v_i}{v_i}$. The condition $v_i(e^\theta-1)<1$ is that strict range, and it also covers $v_i=0$ (every $\theta$). The hypothesis $i\in S$ is implicit on the page (the proof uses $q_i=v_i/\sum_{j\in S}v_j$).
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 32, Lemma A.1 (proof (A.1)–(A.3), p. 33)

import Mathlib
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_EpochLaw

namespace MNLBandit.UCB

open MeasureTheory

theorem lemma_A_1 {N : ℕ} (v : Fin N → ℝ) (hv : ∀ j, 0 ≤ v j) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∈ S) (θ : ℝ) (hθ : v i * (Real.exp θ - 1) < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (epochCount i ω : ℝ))) ∂(epochLaw v S) =
      ENNReal.ofReal (1 / (1 - v i * (Real.exp θ - 1))) := by sorry

end MNLBandit.UCB
