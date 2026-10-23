-- Prove2me | Theorems.Thm_GoTBandit_Main_theorem_V_6
-- name    : GoTBandit.Main.theorem_V_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:17.399361+00:00
-- url     : https://prove2.me/theorems/d51536a3-d3d8-4880-a3e6-23d1eb556bc8
-- title:
--   Theorem V.6, p. 10 — for small ε the optimal GoT state has stationary probability above 1/(2(1−η))
-- statement:
--   Let $2\le M$, $N\le M$, and let $U=(U_{n,i})$ be positive utilities, inducing the game $u_n(a)=U_{n,a_n}\eta_{a_n}(a)$ with a unique optimal profile $a^*$ of $\sum_nu_n(a)$, optimal value $J_1=\sum_nu_n(a^*)$ and $u_{n,\max}=\max_au_n(a)$. Let $z^*=[a^*,C^N]$ be the optimal state of the GoT chain $P^\varepsilon$ on $Z$. If
--
--   $$
--   c>\sum_nu_{n,\max}-J_1,
--   $$
--
--   then for every $0<\eta<\tfrac12$ there is $\varepsilon_0>0$ such that for every $0<\varepsilon<\varepsilon_0$ and every stationary distribution $\pi$ of $P^\varepsilon$,
--
--   $$
--   \pi_{z^*}>\frac1{2(1-\eta)}.
--   $$
--
--   The theorem says that for small perturbation the GoT dynamics spend more than half of the time in the optimal state, which is what makes the majority vote of the exploitation phase correct.
--
--   **Formalization Note** "There exists a small enough $\varepsilon$" is read as a threshold $\varepsilon_0$, as the proof's sufficient condition (63)–(64) and the discussion on p. 10 indicate. "The stationary distribution" is read as every stationary distribution. The hypotheses $M\ge2$ (Eq. (5) divides by $|\mathcal A_n|-1$) and positive utilities (in the algorithm these are the epoch's estimates) are added. The chain is not irreducible on all of $Z$ (a state with a content colliding player cannot be entered), so irreducibility is not assumed. Here $\eta$ is the slack parameter, not the collision indicator.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, p. 10, Theorem V.6 (proof in Appendix A, pp. 15–18)

import Mathlib
import Definitions.Def_GoTBandit_Main_GoTChain

namespace GoTBandit.Main

/-- Theorem V.6, p. 10: if `c > ∑_n u_{n,max} − J1`, then for every `0 < η < 1/2` and every
small enough `ε > 0`, the optimal state `z* = [a*, C^N]` has stationary probability
`π_{z*} > 1/(2(1 − η))` under the GoT dynamics. Disclosed additions: positive utilities and
`M ≥ 2`. -/
theorem theorem_V_6 {N M : ℕ} (hNM : N ≤ M) (hM : 2 ≤ M) (U : Fin N → Fin M → ℝ)
    (hU : ∀ n i, 0 < U n i) (aStar : Fin N → Fin M) (hopt : IsOptimal U aStar)
    (huniq : ∀ a, IsOptimal U a → a = aStar) (c : ℝ)
    (hc : ∑ n, uMax U n - obj U aStar < c) :
    ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ π : Z N M → ℝ, MarkovMixing.IsStationary (gotMatrix U ε c) π →
        1 / (2 * (1 - η)) < π (zStar aStar) := by sorry

end GoTBandit.Main
