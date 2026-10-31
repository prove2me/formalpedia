-- Prove2me | Theorems.Thm_MarkovEntanglementExact_absorbing_step
-- name    : MarkovEntanglementExact.absorbing_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:09.874382+00:00
-- url     : https://prove2.me/theorems/f0c5ad00-dca6-4d42-a974-fd2d1a5519ec
-- title:
--   §3.2, p.11 — the absorbing step $P^t(y\otimes e)=((\sum_jx_jP^{(j)}_A)^ty)\otimes e$
-- statement:
--   Let $P=\sum_{j=1}^Kx_jP^{(j)}_A\otimes P^{(j)}_B$ be as in Definition 1. Then for every $t\ge0$, every $y$ on $S_A$ and every $y'$ on $S_B$,
--   $$P^t(y\otimes e)=\Big(\big(\sum_jx_jP^{(j)}_A\big)^ty\Big)\otimes e,\qquad P^t(e\otimes y')=e\otimes\Big(\big(\sum_jx_jP^{(j)}_B\big)^ty'\Big).$$
--
--   This is the step that turns the global discounted series into the local one, and it rests on $P^{(j)}_Be=e$.
--
--   **Formalization Note** $y\otimes e$ is written `fun q => y q.1`.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: the display is for the reward vector r_A, and "similar results" for B → an arbitrary vector y for each agent, both stated; reason: r_A is an instance
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §3.2, p.11

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- The absorbing step: if `P = Σ_j x_j P^(j)_A ⊗ P^(j)_B`, then for every `t`,
`P^t (y ⊗ e) = ((Σ_j x_j P^(j)_A)^t y) ⊗ e`, and symmetrically
`P^t (e ⊗ y) = e ⊗ ((Σ_j x_j P^(j)_B)^t y)`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §3.2, p.11. The
`N`-agent, one-step form is Lemma 6, p.40, published as
`MarkovEntanglement.separable_apply_local_reward`. -/
theorem absorbing_step
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj) (t : ℕ) :
    (∀ (y : SA → ℝ) (p : SA × SB),
      (P ^ t).mulVec (fun q => y q.1) p = ((∑ k, x k • PAj k) ^ t).mulVec y p.1) ∧
      (∀ (y : SB → ℝ) (p : SA × SB),
        (P ^ t).mulVec (fun q => y q.2) p = ((∑ k, x k • PBj k) ^ t).mulVec y p.2) := by sorry

end MarkovEntanglementExact
