-- Prove2me | Theorems.Thm_KarlinDP_Deterministic_principle_of_optimality
-- name    : KarlinDP.Deterministic.principle_of_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:16:55.356155+00:00
-- url     : https://prove2.me/theorems/6d0c66a4-f9a5-4417-b16d-75402251d8fa
-- title:
--   Functional equation (2), p. 290 — the Principle of Optimality K(ω) = max_{δ₁} {L(ω, δ₁) + P(δ₁) K(T_{δ₁} ω)}
-- statement:
--   In Karlin's deterministic model ($\Omega$ Hausdorff, $D$ nonempty compact Hausdorff, $L \ge 0$ continuous on $\Omega \times D$, $(\delta, \omega) \mapsto T_\delta\,\omega$ continuous, $P > 0$ continuous, $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$), suppose that for every initial state $\omega$ the partial sums (1) of $\Phi(\omega, s) = \sum_n L(\omega_n, \delta_n) P_n(s)$ converge uniformly in $s$. Let $K(\omega) = \max_{S} \Phi(\omega, s)$ be the optimal return. Then for every $\omega \in \Omega$
--   $$K(\omega) = \max_{\delta_1 \in D} \bigl\{ L(\omega, \delta_1) + P(\delta_1)\, K(T_{\delta_1}\,\omega) \bigr\}, \qquad (2)$$
--   and the maximum over $\delta_1$ is attained.
--
--   This is the "Principle of Optimality": the optimal return from $\omega$ is obtained by choosing the best first decision and continuing optimally from the resulting state. It is the general form of the functional equation used throughout dynamic programming.
--
--   **Formalization Note** $K(\omega)$ is written as the supremum of $\Phi(\omega, \cdot)$ over all strategies `s : ℕ → D`; under the hypotheses, $\Phi(\omega,\cdot)$ is continuous on the compact strategy space, so this supremum is a maximum. The conclusion is `IsGreatest`: $K(\omega)$ belongs to the set of values $L(\omega, \delta) + P(\delta) K(T_\delta\,\omega)$, $\delta \in D$, and bounds it from above. Joint continuity of $T$ and nonemptiness of $D$ are assumed as in Theorem 1.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, p. 290, §Functional Equation for the Optimal Strategy, eq. (2) (printed slip t_{δ_1} read as T_{δ_1})

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

namespace KarlinDP.Deterministic

/-- The functional equation (2), "the Principle of Optimality" (Karlin 1955, p. 290): if the
series (1) converges uniformly in `S` for each `ω`, the optimal return
`K(ω) = max_S Φ(ω, s)` satisfies `K(ω) = max_{δ₁} {L(ω, δ₁) + P(δ₁) K(T_{δ₁} ω)}`, the
maximum over `δ₁` being attained. -/
theorem principle_of_optimality {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (hunif : ∀ ω, TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω)
      Filter.atTop) :
    ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * optimalReturn L T P (T δ ω))
      (optimalReturn L T P ω) := by sorry

end KarlinDP.Deterministic
