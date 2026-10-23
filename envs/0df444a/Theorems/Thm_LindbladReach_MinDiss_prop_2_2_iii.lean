-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_prop_2_2_iii
-- name    : LindbladReach.MinDiss.prop_2_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:39.050096+00:00
-- url     : https://prove2.me/theorems/75e2da0c-f479-402b-884b-e8f769470e02
-- title:
--   Proposition 2.2(iii), p. 5 — conjugated jumps e^{tL_{Ad_u(a)}} and e^{tΣ_j L_{Ad_{u_j}(a_j)}} are in the closed class Channel(S)
-- statement:
--   Let $H=\mathbb C^{2^k}$ and let $S$ be a set of operators on $H$ that generates a Hörmander system. For $a\in S$ and a unitary $u$, write $\operatorname{Ad}_u(a)=uau^*$. Then:
--
--   1. for every $a\in S$, every unitary $u$ and every $t\ge0$,
--   $$e^{tL_{\operatorname{Ad}_u(a)}}\in\overline{\mathrm{Channel}(S)};$$
--   2. for every finite family $a_1,\dots,a_m\in S$, unitaries $u_1,\dots,u_m$ and every $t\ge0$,
--   $$e^{t\sum_{j}L_{\operatorname{Ad}_{u_j}(a_j)}}\in\overline{\mathrm{Channel}(S)}.$$
--
--   Here $L_a(\rho)=2a\rho a^*-a^*a\rho-\rho a^*a$. The class is closed only under composition and limits, not under sums of generators, and the jumps it starts from are the elements of $S$. The statement says that every unitary rotation of an available jump, and every sum of such rotated generators, is again available. The paper uses this to move the single-qubit jump to any register.
--
--   **Formalization Note** Only part (iii) of Proposition 2.2 is posed. Part (ii) (Trotter, with a Hamiltonian) is not used on the way to Theorem 2.12. The family is indexed by `Fin m`. The dissipator has the standard sign (see the Setting file). Proposition 2.2 prints $\mathrm{Channel}(S)$ without the overline. Membership is posed in the closed class, because the second conjunct is a Trotter limit (as the proof of (ii) says) and every use is in the closed class. $S=S^*$ is not assumed, as on the page.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 5, Proposition 2.2(iii)

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Proposition 2.2(iii), p. 5: conjugated jumps `e^{tL_{Ad_u(a)}}` and the semigroups of sums
`e^{t Σ_j L_{Ad_{u_j}(a_j)}}` lie in the closed class. -/
theorem prop_2_2_iii {k : ℕ} (S : Set (Mat k)) (hH : IsHormander S) :
    (∀ a ∈ S, ∀ U ∈ Matrix.unitaryGroup (Idx k) ℂ, ∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp ((t : ℂ) • dissipator (U * a * Uᴴ)) ∈ channelClosure S) ∧
    (∀ (m : ℕ) (a : Fin m → Mat k) (U : Fin m → Mat k), (∀ j, a j ∈ S) →
      (∀ j, U j ∈ Matrix.unitaryGroup (Idx k) ℂ) → ∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp ((t : ℂ) • ∑ j, dissipator (U j * a j * (U j)ᴴ)) ∈ channelClosure S) := by sorry

end LindbladReach.MinDiss
