-- Prove2me | Theorems.Thm_MarkovEntanglementExact_marginal_identity
-- name    : MarkovEntanglementExact.marginal_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:12.040975+00:00
-- url     : https://prove2.me/theorems/c4a65899-52f5-4728-be43-1f7a44ffcee8
-- title:
--   §3.2, p.10 — the marginal identity; $\sum_j x_jP^{(j)}_A$ is a transition matrix
-- statement:
--   Let $P$ be a transition matrix on $S_A\times S_B$ with $P=\sum_{j=1}^Kx_jP^{(j)}_A\otimes P^{(j)}_B$, as in Definition 1, where $S_A,S_B$ are nonempty. Then for all $a,a',b$,
--   $$\sum_{b'}P\big((a',b')\mid(a,b)\big)=\sum_{j=1}^Kx_jP^{(j)}_A(a'\mid a),$$
--   so the left side does not depend on $b$. The symmetric identity holds for agent $B$. In particular, $\sum_jx_jP^{(j)}_A$ and $\sum_jx_jP^{(j)}_B$ are transition matrices.
--
--   The second conclusion is not automatic, since the $x_j$ may be negative: the nonnegativity of the sum comes from that of $P$. The identity is also a test for entanglement, since a row marginal of $P$ that depends on $b$ rules out separability.
--
--   **Formalization Note** Nonemptiness of the two sets excludes only the case of an empty factor, where $P$ is the empty matrix and gives no information on the signed sum of the other factor.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: the identity appears as the middle of a computation of P^π_A, with μ summed out → the row-marginal identity at every b, plus the conclusion that both signed sums are transition matrices; reason: it implies the printed computation, and the transition-matrix conclusion follows from P ≥ 0
--   - encoding: state-action spaces of an MDP, implicitly nonempty → [Nonempty SA] [Nonempty SB]; reason: this only excludes an empty factor, for which the signed sum of the other factor can have negative entries
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §3.2, p.10

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- The marginal identity: if a transition matrix `P` decomposes as
`Σ_j x_j P^(j)_A ⊗ P^(j)_B`, then at every `(a, b)` the row of `P` summed over `b'` is
`Σ_j x_j P^(j)_A(a, ·)`, not depending on `b`, and symmetrically for agent `B`. Hence
`Σ_j x_j P^(j)_A` and `Σ_j x_j P^(j)_B` are transition matrices, even though the `x_j` are signed.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §3.2, p.10.

**Formalization Note.** The state-action spaces are nonempty. This excludes only the degenerate
case of an empty factor, where `P` is the empty matrix and says nothing about the other factor's
signed sum. -/
theorem marginal_identity
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    [Nonempty SA] [Nonempty SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj) :
    (∀ a a' b, ∑ b', P (a, b) (a', b') = (∑ k, x k • PAj k) a a') ∧
      (∀ a b b', ∑ a', P (a, b) (a', b') = (∑ k, x k • PBj k) b b') ∧
      IsTransitionMatrix (∑ k, x k • PAj k) ∧
      IsTransitionMatrix (∑ k, x k • PBj k) := by sorry

end MarkovEntanglementExact
