-- Prove2me | Theorems.Thm_GenSwitchHT_lemma_1
-- name    : GenSwitchHT.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:28.788163+00:00
-- url     : https://prove2.me/theorems/813fc92e-2cc8-4ec0-bae0-ad21f1b11a6b
-- title:
--   Lemma 1 — MaxWeight attains the support function of the capacity region
-- statement:
--   Let $q\in\mathbb R^n$. Suppose that in each channel state $m$ the service vector $s$ is drawn from a law supported on $\arg\max_{x\in\mathcal S^{(m)}}\langle q,x\rangle$, with the channel state distributed as $\psi$. Then
--
--   $$
--   \mathbb E_q\bigl[\langle q,s\rangle\bigr]=\max_{x\in\mathcal C}\langle q,x\rangle .
--   $$
--
--   So the expected service rate of MaxWeight is a maximizer direction of the capacity region, even though a single schedule need not lie in $\mathcal C$. This is the first step of every drift bound for the system.
--
--   Differences from the source:
--   - generalization: a generalized switch under MaxWeight with ties at random, at a queue state q → any G, any real vector q, and any law of the schedule on the arg max; reason: random tie-breaking and nonnegative q are instances
--   - encoding: max → IsGreatest of the image of C under ⟨q,·⟩; reason: it records that the maximum is attained
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Lemma 1, p.6

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology

namespace GenSwitchHT

/-- Lemma 1 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete
Resource Pooling, arXiv:1904.10096v4, p.6: under MaxWeight, `E_q[⟨q(k), s(k)⟩] = max_{x ∈ C} ⟨q, x⟩`.

**Formalization Note.** `σ m` is the law of the schedule given the queue vector `q` and the channel
state `m`, any law on the arg max of eq. (4). The service vector then has law `G.ψ.bind σ`. The
maximum is stated with `IsGreatest`, so that it is attained. -/
theorem lemma_1 {n : ℕ} {M : Type*} [Fintype M] (G : Switch n M) (q : Fin n → ℝ)
    (σ : M → PMF (Fin n → ℝ)) (hσ : ∀ m, ∀ x ∈ (σ m).support, IsMaxWeight G q m x) :
    IsGreatest ((fun x => q ⬝ᵥ x) '' G.capacityRegion)
      (expect (G.ψ.bind σ) fun s => q ⬝ᵥ s) := by sorry

end GenSwitchHT
