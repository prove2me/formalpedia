-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_zeta_characterization
-- name    : NetFeePlatform.InteropDominance.zeta_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:05.971731+00:00
-- url     : https://prove2.me/theorems/166d9880-1ff8-48aa-a4ff-9bac9f060f16
-- title:
--   Appendix E.2, proof of Proposition 6, p. 51 — duopoly equilibrium shares under λ are the zeros of ζ(·; λ)
-- statement:
--   Consider the Logit duopoly without outside option, with marginal cost $c$, network-interaction value $\gamma$ and interoperability $\lambda$, and let
--   $\zeta(n;\lambda)=\ln\frac{n}{1-n}+\frac1{1-n}-\frac1n-2\gamma(1-\lambda)(2n-1)$.
--
--   1. If $t$ is a Nash equilibrium in net fees, then both equilibrium shares are zeros of $\zeta$:
--   $$\zeta(n^j(t);\lambda)=0\qquad(j=1,2).$$
--   2. Conversely, if $0\le\lambda\le1$, $\gamma(1-\lambda)\le 27/8$, and $n\in(0,1)$ satisfies $\zeta(n;\lambda)=0$, then for each platform $j$ there is a Nash equilibrium $t$ in which $j$'s market share is exactly $n$.
--
--   Part 1 combines the two first-order conditions (20) with $e^{-t^1}/e^{-t^2}=n^1/n^2$ and $n^2=1-n^1$; part 2 is the step "whose zeros are equilibria", which the proof of Proposition 6 uses.
--
--   **Formalization Note** Part 2 carries the hypothesis $\gamma(1-\lambda)\le 27/8$ under which the paper establishes that the first-order condition is sufficient (Appendix E.1.3 with (36)); the proof on p. 51 treats a zero of $\zeta$ as an equilibrium without restating it. Part 1 needs no hypothesis.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 51, Appendix E.2, proof of Proposition 6

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropDominance_Zeta

namespace NetFeePlatform.InteropDominance

theorem zeta_characterization (c γ lam : ℝ) :
    (∀ t : Fin 2 → ℝ, NetFeePlatform.Competition.IsEquilibrium 0 c γ lam t → ∀ j : Fin 2, zeta γ lam (NetFeePlatform.Competition.demand 0 t j) = 0) ∧
    (0 ≤ lam → lam ≤ 1 → γ * (1 - lam) ≤ 27 / 8 →
      ∀ n : ℝ, 0 < n → n < 1 → zeta γ lam n = 0 →
        ∀ j : Fin 2, ∃ t : Fin 2 → ℝ, NetFeePlatform.Competition.IsEquilibrium 0 c γ lam t ∧ NetFeePlatform.Competition.demand 0 t j = n) := by sorry

end NetFeePlatform.InteropDominance
