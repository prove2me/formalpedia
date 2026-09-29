-- Prove2me | Theorems.Thm_MonotoneDP_Increase_prop11_convergence_characterization
-- name    : MonotoneDP.Increase.prop11_convergence_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:00:35.653918+00:00
-- url     : https://prove2.me/theorems/2cba8eaa-9924-4c9f-817a-5e045ae250f5
-- title:
--   Proposition 11 — J_∞ = J* iff projection and intersection commute: conditions (66) and (68)
-- statement:
--   Let $(S,C,U,H,\bar J)$ be a monotone model satisfying Assumptions I, I.1 and I.2, with $J_\infty$, $C_k$, $P(\cdot)$ and $\overline{\,\cdot\,}$ as in the mission's definitions (all intersections are over $k\ge1$).
--
--   **(a)** Each of $J_\infty=T(J_\infty)$ and $J_\infty=J^*$ holds if and only if
--
--   $$\overline{P\Bigl(\bigcap_{k=1}^\infty C_k\Bigr)}=\bigcap_{k=1}^\infty\overline{P(C_k)}.\tag{66}$$
--
--   **(b)** The conjunction "$J_\infty=T(J_\infty)$, and for each $x\in S$ the infimum in $J_\infty(x)=\inf_{u\in U(x)}H(x,u,J_\infty)$ is attained" holds if and only if
--
--   $$P\Bigl(\bigcap_{k=1}^\infty C_k\Bigr)=\bigcap_{k=1}^\infty\overline{P(C_k)}.\tag{68}$$
--
--   Equivalently, $J_\infty=J^*$ and there exists an optimal stationary policy if and only if (68) holds.
--
--   Convergence of the dynamic programming algorithm, which amounts to interchanging a limit and an infimum over policies, is thereby equivalent to interchanging projection and intersection of the sets $C_k$.
--
--   **Formalization Note** The page's parentheticals are rendered as follows. "(equivalently $J_\infty=J^*$)" is Proposition 10, and appears as the second equivalence in (a) and in the last sentence of (b). "(equivalently there exists an optimal stationary policy)" is equivalent to attainment in (67) only together with $J_\infty=J^*$ (the paper itself cites an example with an optimal stationary policy and $J_\infty\ne J^*$), so it is stated jointly with $J_\infty=J^*$ and never as an equivalence of (68) with the bare existence of an optimal stationary policy.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 458 (PDF p. 21), Proposition 11, eqs. (62)–(63), (66)–(68). DOI 10.1137/0315031

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Increase_Epigraph

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 458, Proposition 11: under I, I.1 and I.2,
(a) `J_∞ = T(J_∞)` (equivalently `J_∞ = J*`) iff
`\overline{P(⋂_{k≥1} C_k)} = ⋂_{k≥1} \overline{P(C_k)}` (eq. (66));
(b) `J_∞ = T(J_∞)` and the infimum in `J_∞(x) = inf_{u ∈ U(x)} H(x, u, J_∞)` (eq. (67)) is
attained for each `x` iff `P(⋂_{k≥1} C_k) = ⋂_{k≥1} \overline{P(C_k)}` (eq. (68)); equivalently,
`J_∞ = J*` and there exists an optimal stationary policy iff (68). -/
theorem prop11_convergence_characterization {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ((m.Jinf = m.T m.Jinf ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k)) = ⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      (m.Jinf = m.Jstar ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k)) = ⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) ∧
    (((m.Jinf = m.T m.Jinf ∧
          ∀ x : S, ∃ u ∈ m.U x, m.H x u m.Jinf = ⨅ v ∈ m.U x, m.H x v m.Jinf) ↔
        m.P (⋂ k ≥ 1, m.Ck k) = ⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      ((m.Jinf = m.Jstar ∧ ∃ μ : m.Selector, m.Jmu μ = m.Jstar) ↔
        m.P (⋂ k ≥ 1, m.Ck k) = ⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) := by sorry

end MonotoneDP.Increase
