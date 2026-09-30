-- Prove2me | Theorems.Thm_KarlinDP_Deterministic_solution_nstep_expansion
-- name    : KarlinDP.Deterministic.solution_nstep_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:17:28.628573+00:00
-- url     : https://prove2.me/theorems/e0eb1022-db79-4e55-a756-fae462086c9c
-- title:
--   n-step expansion (p. 291) — a solution M of (2) equals max over δ₁,…,δₙ of the n-stage yield plus M(ω_{n+1})P_{n+1}(s)
-- statement:
--   In Karlin's deterministic model ($\Omega$ Hausdorff, $D$ nonempty compact Hausdorff, $L \ge 0$ continuous on $\Omega \times D$, $(\delta, \omega) \mapsto T_\delta\,\omega$ continuous, $P > 0$ continuous, $\omega_1 = \omega$, $\omega_n = T_{\delta_{n-1}}\,\omega_{n-1}$, $P_n(s) = \prod_{i=1}^{n-1} P(\delta_i)$), let $M : \Omega \to \mathbb{R}$ solve the functional equation
--   $$M(\omega) = \max_{\delta \in D} \bigl\{ L(\omega, \delta) + P(\delta)\, M(T_\delta\,\omega) \bigr\} \quad \text{for every } \omega,$$
--   with the maximum attained. Then for every $n \ge 0$ and every $\omega$
--   $$M(\omega) = \max_{\delta_1, \dots, \delta_n} \Bigl\{ \sum_{m=1}^{n} L(\omega_m, \delta_m)\, P_m(s) + M(\omega_{n+1})\, P_{n+1}(s) \Bigr\},$$
--   the maximum being attained. The paper writes out the case $n = 2$, where the last term is $P(\delta_1) P(\delta_2) M(\omega_3)$.
--
--   Iterating the functional equation in this way expresses $M$ as an $n$-stage optimization problem with terminal reward $M$; letting $n \to \infty$ is the route to the uniqueness theorem.
--
--   **Formalization Note** The maximum is taken over full strategies `s : ℕ → D`, of which only `s 0, …, s (n-1)` (the paper's $\delta_1, \dots, \delta_n$) enter the expression. Lean's index $n$ gives `partialYield … n` $= \sum_{m=1}^{n} L(\omega_m,\delta_m)P_m(s)$ and `trajectory T ω s n` $= \omega_{n+1}$, `weight P s n` $= P_{n+1}(s)$. No topological hypothesis is needed for this statement; the model's standing hypotheses are kept as in every item of the mission.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Res. Logist. Quart. 2(4), 1955, p. 291, §Uniqueness, first display (the case n = 2, iterated in the "Therefore" step)

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model

namespace KarlinDP.Deterministic

/-- The `n`-step expansion of a solution of (2) (Karlin 1955, p. 291, first display, printed for
`n = 2`): if `M(ω) = max_{δ} {L(ω, δ) + P(δ) M(T_δ ω)}` for every `ω`, then for every `n`,
`M(ω) = max_{δ₁,…,δₙ} {∑_{m=1}^{n} L(ω_m, δ_m) P_m(s) + M(ω_{n+1}) P_{n+1}(s)}`.
The range is over full strategies `s`, of which only `s 0, …, s (n-1)` enter. -/
theorem solution_nstep_expansion {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [CompactSpace D] [T2Space D] [Nonempty D]
    (L : Ω → D → ℝ) (T : D → Ω → Ω) (P : D → ℝ)
    (hL0 : ∀ ω δ, 0 ≤ L ω δ) (hL : Continuous (fun p : Ω × D => L p.1 p.2))
    (hT : Continuous (fun p : D × Ω => T p.1 p.2))
    (hP0 : ∀ δ, 0 < P δ) (hP : Continuous P)
    (M : Ω → ℝ)
    (hM : ∀ ω, IsGreatest (Set.range fun δ => L ω δ + P δ * M (T δ ω)) (M ω)) :
    ∀ n ω, IsGreatest
      (Set.range fun s : ℕ → D => partialYield L T P ω s n + M (trajectory T ω s n) * weight P s n)
      (M ω) := by sorry

end KarlinDP.Deterministic
