-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_lemma_1
-- name    : JSQHalfinWhitt.Tightness.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:48.318947+00:00
-- url     : https://prove2.me/theorems/bdb173c4-4168-4c5f-a090-b18a820ea2a4
-- title:
--   Lemma 1 — basic adjoint relation $\mathbb E\,G_Qf(Q) = 0$
-- statement:
--   Consider the join-the-shortest-queue chain with $n \ge 1$ servers and arrival rate $n\lambda$, $\lambda \in (0,1)$, on the state space $S$, with generator $G_Q$. Let $Q$ have a stationary distribution $\pi$ of the chain. For every function $f : S \to \mathbb R$ with $\mathbb E|f(Q)| < \infty$, the expectation of $G_Q f(Q)$ exists and
--   $$\mathbb E\,G_Q f(Q) = 0. \tag{3.1}$$
--
--   This relation between the generator and the stationary distribution is the tool behind every stationary bound in the paper: choosing test functions $f$ turns (3.1) into identities and inequalities for stationary moments.
--
--   **Formalization Note** $\pi$ is a probability on $S$ satisfying global balance $\pi G_Q = 0$ (see the definition file). $\mathbb E|f(Q)| < \infty$ is the summability of $q \mapsto \pi(q)|f(q)|$; the conclusion asserts the summability of $q \mapsto \pi(q) G_Q f(q)$ and that its sum is $0$. The model's standing assumptions $n \ge 1$ and $0 < \lambda < 1$ are hypotheses.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 6, Lemma 1, (3.1)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

/-- Lemma 1 (Braverman, p. 6): the basic adjoint relation. If `π` is a stationary distribution of
the JSQ chain with `n ≥ 1` servers and `λ ∈ (0, 1)`, and `f : S → ℝ` has `E|f(Q)| < ∞`, then
`E G_Q f(Q)` exists and equals `0`. -/
theorem lemma_1 (n : ℕ) (lam : ℝ) (hn : 1 ≤ n) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (π : State n → ℝ) (hπ : IsStationaryDist (genQ n lam) π)
    (f : State n → ℝ) (hf : Summable (fun q => π q * |f q|)) :
    Summable (fun q => π q * genQ n lam f q) ∧ expect π (genQ n lam f) = 0 := by sorry

end JSQHalfinWhitt.Tightness
