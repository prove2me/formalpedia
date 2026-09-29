-- Prove2me | Theorems.Thm_KServer_wfaU_potential_criterion
-- name    : KServer.wfaU_potential_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:15:27.003161+00:00
-- url     : https://prove2.me/theorems/22a55aa6-a56a-4cda-b658-4ce413ad6abf
-- title:
--   The potential-function criterion for the classical Work Function Algorithm
-- statement:
--   Let $w_\tau$ denote the (unlabelled) work function of the request history $\tau$ from the initial configuration $C_0$, and let $C \ge 0$. Suppose there is a function $\Phi$ of the request history satisfying, for every history $\tau$, every request $s$ and every configuration $X$:
--
--   **Offset property.** $\quad 0 \;\le\; \Phi(\tau) + (C+1)\, w_\tau(X);$
--
--   **Update property.** $\quad w_{\tau s}(X) \;\le\; w_\tau(X) + \bigl(\Phi(\tau) - \Phi(\tau s)\bigr).$
--
--   Then the classical Work Function Algorithm is $C$-competitive.
--
--   ## Role
--
--   This is the potential-function method for the Work Function Algorithm in its standard form: Lemma 3 of Bein--Chrobak--Larmore, and the schema instantiated by Coester and Koutsoupias. The update property says the potential drops by at least the largest one-request increase of the work function --- the *extended cost* --- and the offset property says the accumulated drop is repaid, up to a constant, by $(C+1)$ times the optimal offline cost, since $\mathrm{OPT} = \min_X w_\sigma(X)$. Feeding the drops as budgets into the growth lemma for the classical algorithm and telescoping yields $\mathrm{cost} + \mathrm{OPT} \le (C+1)\mathrm{OPT} + a$, hence $C$-competitiveness.
--
--   Concretely, the Coester--Koutsoupias potential for $k = 3$ on trees --- built from work-function values at antipodally extended configurations --- satisfies the offset property with $C + 1 = 4$ outright, and its update property on trees is the content of their Theorem 19/23 chain; through this criterion that yields $3$-competitiveness of WFA for three servers on trees.
--
--   The criterion is stated for the algorithm built from, and analysed against, the **unlabelled** work function --- the same $w$ in the algorithm's minimisation and in both properties. This alignment is essential: for the labelled variant of the algorithm no potential can satisfy the two properties with $C = 3$ on trees, as the required total budget exceeds $4\,\mathrm{OPT}$ by a linearly growing margin.
--
--   ## Formalization note
--
--   $\Phi$ is a function of the request history (a list), so potentials depending on the work function itself are covered by composing with $\tau \mapsto w_\tau$. The additive constant produced is $\Phi([\,])$. `IsCompetitive` is the usual $\exists a, \forall \sigma, \mathrm{cost} \le C \cdot \mathrm{OPT} + a$; the proof of the offset-to-OPT step approximates the infimum defining `offlineCost` by work-function values, so no attainment of the offline optimum is assumed.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, 'The 3-server problem in the plane', Theoretical Computer Science 289 (2002), Lemma 3; the same schema is the potential method of C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, Section 3.

import Mathlib
import Definitions.Def_KServer_wfaU

namespace KServer

theorem wfaU_potential_criterion (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFAU hk C₀) C := by sorry

end KServer
