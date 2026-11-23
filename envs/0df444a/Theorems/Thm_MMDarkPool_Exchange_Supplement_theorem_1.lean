-- Prove2me | Theorems.Thm_MMDarkPool_Exchange_Supplement_theorem_1
-- name    : MMDarkPool.Exchange.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:22:51.549076+00:00
-- url     : https://prove2.me/theorems/23f3319a-fee9-4438-a2a8-b05f6795b0fc
-- title:
--   Theorem 1 (first assertion), p. 8 — unique viscosity solution of the market maker’s HJB (3.2)
-- statement:
--   Let $T>0$ be the horizon, $\mathcal T>0$ the tick, $\sigma,\gamma,\epsilon>0$, and $A^j,\theta^j,\Gamma^j>0$ for $j\in\{l,d\}$, with $\Gamma^l\ge\Gamma^d$. Let $\bar q$ be real with $2\bar q\in\mathbb N$, and let $\mathcal V^l,\mathcal V^d$ be arbitrary finite subsets of $\mathbb N$. Use the real control box $O=[0,2\bar q]^4$ and the intensities, latency weights and Hamiltonian $F$ defined from (3.2) in Model. Then
--   $$
--   \begin{cases}
--   0=\partial_t v(t,q)+F(q,v(t,\cdot)),&t\in(0,T),\ q\in\mathbb Z,\\
--   v(T,q)=-1,&q\in\mathbb Z
--   \end{cases}
--   $$
--   has a viscosity solution, and any two such solutions agree at every $(t,q)\in[0,T]\times\mathbb Z$. Viscosity solution includes continuity in time for every integer inventory. Values outside the time interval are immaterial to the uniqueness assertion.
--
--   This is the first assertion of Theorem 1, concerning the market maker without intervention by the exchange. It is a companion theorem and is not used to prove the mission's published exchange-HJB goal.
--
--   **Formalization Note.** The equation is imposed on all integer inventories so every jump destination is constrained, including overshoots of $\pm\bar q$. The control supremum remains over the real box printed on p. 8, without the sum constraint of $\mathcal A$ or the base mission's inventory-preserving admissibility; sizes not in $\mathcal V^j$ switch off the corresponding intensities. Half-integer risk limits, zero risk limit, and volume sets excluding zero or empty are retained. The viscosity convention uses $C^1$ tests only at interior times, backward signs, and the solution's row as its nonlocal argument. The Hamiltonian is extended-real-valued to preserve the supremum. The identity $V^{\mathrm{MM}}_0=v(0,Q_0)$ and the characterization of optimal controls in the remaining sentences of Theorem 1 are not stated here, because they fail as printed: $V^{\mathrm{MM}}_0$ is a supremum of expectations under the controlled measures $\mathbb P^{\mathcal L}$ of p. 5, and the companion item `controlled_measure_refutation` shows that the printed specification of those measures (size-specific intensities together with the printed density) cannot be met for an admissible control of a parameter instance satisfying every standing assumption. The mission states that refutation in place of these clauses (DISPROOF.md). A repaired model would in addition need the joint law of the latency marks of p. 7 relative to the filtration of p. 4, which the paper does not give (HARD.md). Those clauses are neither assumed nor claimed here. No extra smallness hypothesis on $\epsilon$ or $\Gamma$ is added.
--
--   Differences from the source:
--   - reading: The domain of q in (3.2) is not specified; the jumps use q − φ(i)k. → The equation and uniqueness are posed on [0,T] × ℤ.; reason: Q is integer-valued by §2.2.1; all jump destinations then belong to the equation domain. No grid extension is left arbitrary.
--   - reading: The printed sum in (3.2) runs over Vˡ × Vᵈ, repeating the pool-specific terms. → One sum over Vˡ for lit fills and one over Vᵈ for dark fills.; reason: Each counting process contributes once, consistently with the single-counting reading of the published base model and the per-process sum in (4.16).
--   - reading: Theorem 1 says viscosity solution without defining the notion. → Componentwise C¹ tests at interior times, backward signs ≥ 0 at maxima and ≤ 0 at minima, and coupling evaluated on v(t,·). Continuity and terminal data are required.; reason: This fixes the time-only solution notion, using the published base convention without importing its grid.
--   - generalization: ε is called small enough (p. 4), and Γˡ, Γᵈ small relative to the tick (Remark 2.2). → All positive ε and impacts Γˡ ≥ Γᵈ > 0 are allowed, with no smallness premise.; reason: The paper gives no thresholds. The bounded-control, finite-range Lipschitz Hamiltonian is well posed for every such fixed parameter tuple; see MODERATION_NOTES.md.
--   - encoding: A supremum of real jump payoffs over O is used in (3.2). → The supremum and risk term are combined in EReal; all solution values remain real.; reason: This preserves the mathematical supremum even before boundedness is proved and avoids the default value of an unbounded real supremum.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, p. 8, Theorem 1 (first assertion), equation (3.2); governing assumptions §2, pp. 4–7; proof pointer p. 8 to Appendix A.3, pp. 29–30.

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Supplement_Model

namespace MMDarkPool.Exchange.Supplement

theorem theorem_1 (P : Params) (hP : Standing P) : ∃ v : ℝ → ℤ → ℝ, IsViscositySolution P v ∧ ∀ w : ℝ → ℤ → ℝ, IsViscositySolution P w → ∀ t ∈ Set.Icc 0 P.T, ∀ q : ℤ, w t q = v t q := by sorry

end MMDarkPool.Exchange.Supplement
