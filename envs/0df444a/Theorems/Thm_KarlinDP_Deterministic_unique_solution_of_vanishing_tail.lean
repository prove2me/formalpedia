-- Prove2me | Theorems.Thm_KarlinDP_Deterministic_unique_solution_of_vanishing_tail
-- name    : KarlinDP.Deterministic.unique_solution_of_vanishing_tail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:17:55.387985+00:00
-- url     : https://prove2.me/theorems/6b802307-36ef-445b-88d2-a3a1007d0a81
-- title:
--   Uniqueness (pp. 290–291) — a solution of (2) with vanishing tail is K(ω) = max_S Φ(ω, s)
-- statement:
--   Let $\Omega$ be a Hausdorff space and $D$ a nonempty compact Hausdorff space, let $L : \Omega \times D \to \mathbb{R}$ be continuous and non-negative, let $(\delta, \omega) \mapsto T_\delta\,\omega$ be continuous, and let $P : D \to \mathbb{R}$ be continuous and positive. For a strategy $s = (\delta_1, \delta_2, \dots)$ put $\omega_1 = \omega$, $\omega_n = T_{\delta_{n-1}}\,\omega_{n-1}$, $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$ and $\Phi(\omega, s) = \sum_{n \ge 1} L(\omega_n, \delta_n) P_n(s)$, and assume that for every $\omega$ the partial sums of this series converge uniformly in $s$.
--
--   Let $M : \Omega \to \mathbb{R}$ satisfy:
--   1. the functional equation (2), with the maximum attained:
--   $$M(\omega) = \max_{\delta \in D} \bigl\{ L(\omega, \delta) + P(\delta)\, M(T_\delta\,\omega) \bigr\} \quad \text{for every } \omega;$$
--   2. the vanishing-tail condition: for every $\omega$,
--   $$\lim_{n \to \infty} \ \sup_{\delta_1, \dots, \delta_n} \bigl| M(\omega_n) \bigr| \prod_{i=1}^{n-1} P(\delta_i) = 0.$$
--
--   Then for every $\omega \in \Omega$
--   $$M(\omega) = \max_{s \in S} \Phi(\omega, s) = K(\omega),$$
--   and the maximum is attained by some strategy.
--
--   This is the uniqueness theorem for the functional equation: among solutions whose tail term vanishes, the optimal return is the only one. It licenses the usual practice of dynamic programming, which starts from a solution of the functional equation and reads off properties of optimal strategies.
--
--   **Formalization Note** The paper leaves the class of admissible $M$ open ("an appropriate class of M's for which the lim = 0") and checks it in its two examples (bounded $M$ with a discount $\alpha < 1$; continuous $M$ vanishing at the origin with $\omega_n \to 0$), both of which give the two-sided decay $\sup_s |M(\omega_n)| P_n(s) \to 0$ used here. In Lean the tail condition reads: for every $\omega$ and $\varepsilon > 0$ there is $N$ such that $|M(\omega_n)|\,P_n(s) \le \varepsilon$ for all $n \ge N$ and all strategies $s$. Joint continuity of $T$ and nonemptiness of $D$ are assumed as in Theorem 1. Strategies are `s : ℕ → D`, Lean index $k$ is stage $k+1$, and "maximum" is `IsGreatest` of the range of $\Phi(\omega,\cdot)$.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, pp. 290–291, §Uniqueness (the "Therefore" display of p. 291 and the requirement that the limit term be zero)

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

namespace KarlinDP.Deterministic

/-- Uniqueness (Karlin 1955, pp. 290–291): if the series (1) converges uniformly in `S` for each
`ω`, and `M` solves the functional equation (2) with the limit term vanishing, in the two-sided
form `sup_s |M(ω_n)| P_n(s) → 0`, then `M(ω) = max_S Φ(ω, s)` for every `ω`, the maximum being
attained. -/
theorem unique_solution_of_vanishing_tail {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (hunif : ∀ ω, TendstoUniformly (fun k s => partialYield L T P ω s k) (totalYield L T P ω)
      Filter.atTop)
    (M : Ω → ℝ)
    (hM : ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * M (T δ ω)) (M ω))
    (htail : ∀ ω, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ s : ℕ → D,
      |M (trajectory T ω s n)| * weight P s n ≤ ε) :
    ∀ ω, IsGreatest (Set.range (totalYield L T P ω)) (M ω) := by sorry

end KarlinDP.Deterministic
