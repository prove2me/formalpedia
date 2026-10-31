-- Prove2me | Theorems.Thm_MarkovEntanglementExact_exact_value_decomposition_iff_separable
-- name    : MarkovEntanglementExact.exact_value_decomposition_iff_separable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:22.715306+00:00
-- url     : https://prove2.me/theorems/2cc370d0-5f92-4968-9e1d-c8db4839aa78
-- title:
--   Theorems 1 and 2 — exact value decomposition for every reward holds iff the agents are separable, with the marginalized local Q-values as the decomposition
-- statement:
--   Consider a two-agent MDP with finite state sets $S_A,S_B$, feasible action sets, transition kernel $P$ and policy $\pi$, and let $P^\pi_{AB}$ be the induced transition matrix on joint state-action pairs. Let $0\le\gamma<1$. Then:
--
--   1. (Theorem 1) if the two agents are separable, the exact value decomposition holds: there are maps $\hat Q_A,\hat Q_B$, each reading only its own agent's reward, with
--   $$Q^\pi_{AB}=\hat Q_A(r_A)\otimes e+e\otimes\hat Q_B(r_B)\quad\text{for all } r_A,r_B;$$
--   2. (Theorem 2) if $\gamma>0$ and such maps exist, the two agents are separable;
--   3. for every distribution $\mu$ on joint pairs with positive agent marginals, as in footnote 1, and the local transition matrices $P^\pi_A,P^\pi_B$ of Eq. (2):
--      - $P^\pi_A$ and $P^\pi_B$ are transition matrices;
--      - (Theorem 1) for every decomposition $P^\pi_{AB}=\sum_{j=1}^Kx_jP^{(j)}_A\otimes P^{(j)}_B$ as in Definition 1,
--   $$P^\pi_A=\sum_{j=1}^Kx_jP^{(j)}_A,\qquad P^\pi_B=\sum_{j=1}^Kx_jP^{(j)}_B;$$
--      - (Theorem 1) if the two agents are separable, then for all $r_A,r_B$,
--   $$Q^\pi_{AB}=Q^\pi_A\otimes e+e\otimes Q^\pi_B,\qquad Q^\pi_A=(I-\gamma P^\pi_A)^{-1}r_A,\quad Q^\pi_B=(I-\gamma P^\pi_B)^{-1}r_B;$$
--      - (Theorem 2) if $\gamma>0$ and that identity holds for all $r_A,r_B$, the two agents are separable.
--
--   So for $\gamma>0$, separability, the exact decomposition by reward-local maps, and the decomposition by the marginalized local Q-values are equivalent. This is the headline of the paper: "Markov entanglement serves as a sufficient and necessary condition for the exact value decomposition."
--
--   **Formalization Note** The coefficients $x_j$ are signed. The Q-values are the solutions of the Bellman equation, and the local transitions the solutions of Eq. (2): both exist and are unique, by the milestones, so the universal quantifiers are neither vacuous nor free. $\gamma=0$ is allowed in the clauses of Theorem 1, and the clauses of Theorem 2 carry $\gamma>0$ themselves.
--
--   Differences from the source:
--   - generalization: one action set per agent, and |S_A| = |S_B|, |A_A| = |A_B| "for simplicity" → feasible action sets AA s, AB s and unrelated finite state types; reason: footnote 1 restricts the action sets; the constant action set of equal size is the special case AA := fun _ => A
--   - generalization: μ is the stationary occupancy measure of a unichain, unique and strictly positive on states → μ is any distribution on joint pairs with μ ≥ 0, Σμ = 1 and positive agent marginals; reason: the derivation uses only the positivity of the conditioning marginals (footnote 1); the paper's occupancy measure is an instance, proved in the verification file OccupancyInstance
--   - encoding: Eq. (2) with the conditional μ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied through by the marginal; reason: equivalent under positive marginals; the quotient form is proved in M2
--   - encoding: Q-values as the printed expectation, and Q^π_A = (I − γP^π_A)⁻¹ r_A → Q-values as the solutions of IsBellmanQ; reason: M1 proves the solution exists, is unique, and equals the series and the inverse formula
--   - reading: first sum printed Σ_{i=1}^K x_j P^(j)_A → the sum over j of x_j P^(j)_A; reason: the index i is a typo for j, as Definition 1 and the second sum show
--   - reading: "Q_i : r_i → R^{|S||A|}" with Q^π_AB = Q_A(r_A) ⊗ e + e ⊗ Q_B(r_B) for any pair of rewards, and the V-value wording of §1.1 → ∃ maps QA, QB, then ∀ rA rB, for Q-values; reason: §2, p.7 fixes the Q statement; the maps read only their own reward, and Appendix E shows the other quantifier order fails
--   - reading: "sufficient and necessary", with Theorem 1 at γ ∈ [0, 1) and Theorem 2 at γ > 0 → a conjunction in which only the necessity clauses assume 0 < γ; reason: §4, p.12 names γ = 0 as a trivial counterexample to necessity only
--   - encoding: bounded local rewards |r_i| ≤ r^i_max → all rewards rA, rB on the finite pair types; reason: every function on a finite type is bounded
--   - generalization: Theorem 1 states its conclusion for the local values of the marginalized chains under μ → clause 1 additionally gives reward-local maps for every separable P, with no occupancy measure (the μ form is kept in clause 3); reason: the maps are the Bellman solutions of the transition matrices Σ_j x_j P^(j)_A and Σ_j x_j P^(j)_B (M3), and this is the hypothesis form of Theorem 2 that the equivalence joins to
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, Theorem 2, p.12, and the following sentence, p.12

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsFeasibleKernel
import Definitions.Def_MarkovEntanglementExact_IsFeasiblePolicy
import Definitions.Def_MarkovEntanglementExact_inducedMatrix
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition
import Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- **Exact value decomposition holds for every reward if and only if the agents are separable,
with the marginalized local Q-values as the decomposition** (Theorems 1 and 2 combined).

Let `P = P^π_AB` be the transition matrix of a two-agent MDP with feasible action sets under a
policy `π`, and `0 ≤ γ < 1`. Then:

1. if the agents are separable, the exact decomposition holds with maps reading only their own
   agent's reward (Theorem 1);
2. if `γ > 0` and that decomposition holds, the agents are separable (Theorem 2);
3. for every occupancy `μ` of footnote 1, and the local transition matrices `P_A`, `P_B` of
   Eq. (2): they are transition matrices; for every decomposition
   `P = Σ_j x_j P^(j)_A ⊗ P^(j)_B` they equal `Σ_j x_j P^(j)_A` and `Σ_j x_j P^(j)_B`; if the
   agents are separable, `Q^π_AB = Q^π_A ⊗ e + e ⊗ Q^π_B` for every reward pair; and if `γ > 0`
   and that identity holds for every reward pair, the agents are separable.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, and
Theorem 2, p.12, combined in the sentence following Theorem 2, p.12.

**Formalization Note.** Agent `A`'s state-action pairs are `Σ s, AA s`, with `AA s` the feasible
action set of footnote 1, p.8, and the paper's constant action set is a special case. Q-values
are the solutions of `IsBellmanQ`, which exist and are unique, and local transitions the
solutions of `IsLocalTransitionA/B`, which exist and are unique under `IsOccupancy`, so the
universal quantifiers are neither vacuous nor free. `μ` is not assumed stationary and need not be
unique or strictly positive on joint pairs; the paper's occupancy measure is an instance once the
feasible sets are restricted as in footnote 1. The clauses that need `γ > 0` carry it themselves,
because `γ = 0` is a counterexample to them only (§4, p.12). -/
theorem exact_value_decomposition_iff_separable
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    {AA : SA → Type*} {AB : SB → Type*} [∀ s, Fintype (AA s)] [∀ s, Fintype (AB s)]
    [∀ s, DecidableEq (AA s)] [∀ s, DecidableEq (AB s)]
    (kernel : (s : SA × SB) → AA s.1 × AB s.2 → SA × SB → ℝ)
    (hkernel : IsFeasibleKernel kernel)
    (π : (s : SA × SB) → AA s.1 × AB s.2 → ℝ)
    (hπ : IsFeasiblePolicy π)
    {P : Matrix ((Σ s, AA s) × (Σ s, AB s)) ((Σ s, AA s) × (Σ s, AB s)) ℝ}
    (hP : P = inducedMatrix kernel π)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (IsSeparable P → HasExactValueDecomposition P γ) ∧
      (0 < γ → HasExactValueDecomposition P γ → IsSeparable P) ∧
      ∀ μ : (Σ s, AA s) × (Σ s, AB s) → ℝ, IsOccupancy μ →
        ∀ (PA : Matrix (Σ s, AA s) (Σ s, AA s) ℝ) (PB : Matrix (Σ s, AB s) (Σ s, AB s) ℝ),
          IsLocalTransitionA P μ PA → IsLocalTransitionB P μ PB →
            IsTransitionMatrix PA ∧ IsTransitionMatrix PB ∧
            (∀ (K : ℕ) (x : Fin K → ℝ) (PAj : Fin K → Matrix (Σ s, AA s) (Σ s, AA s) ℝ)
                (PBj : Fin K → Matrix (Σ s, AB s) (Σ s, AB s) ℝ),
              IsSeparableWitness P K x PAj PBj →
                PA = ∑ k, x k • PAj k ∧ PB = ∑ k, x k • PBj k) ∧
            (IsSeparable P → LocalValuesDecompose P PA PB γ) ∧
            (0 < γ → LocalValuesDecompose P PA PB γ → IsSeparable P) := by sorry

end MarkovEntanglementExact
