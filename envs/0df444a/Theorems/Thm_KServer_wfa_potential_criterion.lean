-- Prove2me | Theorems.Thm_KServer_wfa_potential_criterion
-- name    : KServer.wfa_potential_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:11:04.547673+00:00
-- url     : https://prove2.me/theorems/19c0c3e1-e9a9-471b-b1ce-6c4ec486ba14
-- title:
--   Competitiveness of the Work Function Algorithm from a potential
-- statement:
--   Fix an initial configuration $C_0$ on a finite metric space and suppose a real number $\Phi_\sigma$ is assigned to every request sequence $\sigma$. Suppose it satisfies
--
--   * the **offset property** (OP): $\Phi_\sigma + (C+1)\, w_\sigma(X) \ge 0$ for every configuration $X$, and
--   * the **update property** (UP): for every request $s$ and every configuration $X$,
--     $$w_{\sigma s}(X) \;\le\; w_\sigma(X) + \bigl(\Phi_\sigma - \Phi_{\sigma s}\bigr).$$
--
--   Then the **Work Function Algorithm** started at $C_0$ is $C$-competitive.
--
--   ## Role
--
--   This is the criterion in the form the work-function literature actually uses. A companion statement produces *some* $C$-competitive algorithm from the same hypotheses, by way of the extended cost lemma; the present one names the algorithm, and that is what statements like "WFA is $3$-competitive on trees" or "WFA is $3$-competitive in the Manhattan plane" assert.
--
--   The two ingredients are the potential telescoping and the pseudocost method. The update property says the potential pays for the growth of the work function at each step, so the budgets $u_t = \Phi_{\sigma|_t} - \Phi_{\sigma|_{t+1}}$ satisfy the hypothesis of the pseudocost lemma and telescope to $\Phi_\varnothing - \Phi_\sigma$. That lemma then gives
--
--   $$\mathrm{cost}_{\mathrm{WFA}}(\sigma) + \mathrm{opt}(\sigma) \;\le\; \Phi_\varnothing - \Phi_\sigma \;\le\; (C+1)\,\mathrm{opt}(\sigma) + \Phi_\varnothing,$$
--
--   the last step being the offset property at a configuration nearly realising the optimum. Subtracting $\mathrm{opt}(\sigma)$ leaves $C$-competitiveness with additive constant $\Phi_\varnothing$, which does not depend on the request sequence.
--
--   **Formalization note.** Unlike the version routed through the extended cost lemma, this one needs no auxiliary injective configuration: the algorithm is given, not constructed. The offset property is stated for every configuration and only its infimum is used; passing from that infimum to the optimal offline cost is an $\varepsilon$-argument, and $0 \le C$ enters only to know that $C+1$ is positive.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 3, in the form asserting competitiveness of the Work Function Algorithm itself: 'Then WFA is C-competitive on M.'

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_work_function

namespace KServer

theorem wfa_potential_criterion (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFunction C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFunction C₀ (τ ++ [s]) X ≤ workFunction C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFA hk C₀) C := by sorry

end KServer
