-- Prove2me | Theorems.Thm_KarlinDP_Deterministic_exists_optimal_strategy
-- name    : KarlinDP.Deterministic.exists_optimal_strategy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:15:46.913974+00:00
-- url     : https://prove2.me/theorems/e95e33fc-6797-4729-a85a-42fe57905505
-- title:
--   Theorem 1 (p. 287) — an optimal strategy exists if the series (1) converges uniformly in S
-- statement:
--   Let $\Omega$ be a Hausdorff topological space (the states) and $D$ a nonempty compact Hausdorff space (the decisions), and give the strategy space $S = D \times D \times \cdots$ the product topology. Let $L : \Omega \times D \to \mathbb{R}$ be continuous and non-negative, let $(\delta, \omega) \mapsto T_\delta\,\omega$ be continuous, and let $P : D \to \mathbb{R}$ be continuous and positive. For a strategy $s = (\delta_1, \delta_2, \dots)$ put $\omega_1 = \omega$, $\omega_n = T_{\delta_{n-1}}\,\omega_{n-1}$, $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$ and $\Phi(\omega, s) = \sum_{n \ge 1} L(\omega_n, \delta_n) P_n(s)$.
--
--   Fix an initial state $\omega$ and suppose that the partial sums
--   $$\sum_{n=1}^{k} L(\omega_n, \delta_n)\, P_n(s) \qquad (1)$$
--   converge to $\Phi(\omega, s)$ uniformly in $s \in S$ as $k \to \infty$. Then there is an optimal strategy $s^*$:
--   $$\Phi(\omega, s^*) = \max_{s \in S} \Phi(\omega, s).$$
--
--   This is the existence theorem of the paper; the functional equation (2) and the uniqueness theorem are built on the optimal strategies it provides.
--
--   **Formalization Note** Strategies are `s : ℕ → D` and Lean's index $k$ is the paper's stage $k+1$. The paper's assumption (4) asks for continuity of $T_\delta\,\omega$ separately in $\omega$ and in $\delta$; the statement assumes joint continuity of $(\delta, \omega) \mapsto T_\delta\,\omega$, which implies (4) and is needed for the paper's claim (p. 287) that each term $L(\omega_n, \delta_n) P_n(s)$ is continuous in $s$. $D$ is assumed nonempty (otherwise there is no strategy at all). A single return function $L$ is used, as in display (1). "Maximum" is encoded as `IsGreatest` of the range of $\Phi(\omega, \cdot)$, so the maximum is attained.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, p. 287, Theorem 1 (with the standing assumptions (1)–(4) of p. 286, the product form of P_n(s) and display (1) of p. 287)

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

namespace KarlinDP.Deterministic

/-- Theorem 1 (Karlin 1955, p. 287): an optimal strategy exists provided the series (1)
converges uniformly in `S` (here at the given initial state `ω`). -/
theorem exists_optimal_strategy {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (ω : Ω)
    (hunif : TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω) Filter.atTop) :
    ∃ s₀ : ℕ → D, IsGreatest (Set.range (totalYield L T P ω)) (totalYield L T P ω s₀) := by sorry

end KarlinDP.Deterministic
