-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_Supplement_theorem_3
-- name    : JSQHalfinWhitt.Tightness.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:16:05.54046+00:00
-- url     : https://prove2.me/theorems/f28edab2-d1f6-4f5c-afd1-4920b751c7e2
-- title:
--   Theorem 3 — positive recurrence of the reflected JSQ diffusion
-- statement:
--   Fix any $\beta>0$. On $\Omega=(-\infty,0]\times[0,\infty)$, let $Y$ denote the reflected JSQ diffusion specified by (2.1), driven in its first coordinate by standard Brownian motion with coefficient $\sqrt2$, with drift $(-Y_1+Y_2-\beta,-Y_2)$ and reflection direction $(-1,+1)$ at $Y_1=0$. Then
--   $$
--   Y\text{ is positive Harris recurrent.}
--   $$
--   In detail, the diffusion has a strong Markov realization, and every such realization $F$ has a nonzero sigma-finite measure $\varphi$ on $\Omega$ such that, for every measurable $A\subseteq\Omega$ with $\varphi(A)>0$ and every initial state $y\in\Omega$,
--   $$
--   P_y\!\left(\int_0^\infty 1_A(Y(t))\,dt=\infty\right)=1.
--   $$
--   It also has an invariant probability law $\pi$, meaning
--   $$
--   \pi(A)=\int_\Omega P_t(y,A)\,\pi(dy)\qquad(t\ge0)
--   $$
--   for every measurable $A$. All realizations of (2.1) have the same transition probabilities. Thus existence and uniqueness of the diffusion's transition family are explicit obligations in the statement; recurrence is not conditional on a drift certificate or a stationary-law assumption. There are no restrictions on the initial state, and no prelimit parameters $n$ or $\lambda$.
--
--   This is the companion recurrence theorem needed alongside the published tightness result for the steady-state diffusion approximation. The published Theorem 4 supplies an analytic Lyapunov result for a possible proof; establishing its connection to the stochastic process and applying a recurrence criterion remain solver obligations.
--
--   Differences from the source:
--   - encoding: the named diffusion (2.1) is the unique solution in the governing context → existence of a Markov realization, recurrence for every realization, and equality of their transition families; reason: makes the specified process nonvacuous and independent of its probability-space realization; existence and uniqueness are proof obligations, not extra premises
--   - reading: positive recurrent → positive Harris recurrent: a nonzero sigma-finite recurrence measure, almost surely infinite occupation of each positive-measure set from every initial state, and an invariant probability law; reason: uses the standard general-state diffusion meaning required by the brief, consistent with the ergodicity conclusion of Corollary 1 on p. 16
--   - encoding: nonnegative time, domain Omega, and a regulator supported where Y1 equals zero → nonnegative real times, the subtype of published Omega, and a continuous monotone regulator constant on intervals strictly inside Y1 < 0; reason: these are equivalent representations of the continuous reflected diffusion, with no excluded initial states
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 5, Theorem 3, with (2.1); p. 16, Corollary 1

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Supplement_Diffusion

namespace JSQHalfinWhitt.Tightness.Supplement

open MeasureTheory BramsonQueueing.FIFOKelly

/-- Theorem 3, p. 5 (and Corollary 1, p. 16): the diffusion (2.1) is
positive Harris recurrent. Existence and uniqueness of its transition family
make the process unambiguous and preclude a vacuous conditional theorem. -/
theorem theorem_3 (β : ℝ) (hβ : 0 < β) :
    (∃ (Ξ : Type) (mΞ : MeasurableSpace Ξ),
      letI := mΞ
      ∃ F : MarkovFamily State Ξ, IsJSQDiffusion β F) ∧
    (∀ (Ξ : Type) (mΞ : MeasurableSpace Ξ),
      letI := mΞ
      ∀ F : MarkovFamily State Ξ, IsJSQDiffusion β F → PositiveHarris F) ∧
    (∀ (Ξ Ξ' : Type) (mΞ : MeasurableSpace Ξ) (mΞ' : MeasurableSpace Ξ'),
      letI := mΞ
      letI := mΞ'
      ∀ (F : MarkovFamily State Ξ) (G : MarkovFamily State Ξ'),
        IsJSQDiffusion β F → IsJSQDiffusion β G → F.transition = G.transition) := by sorry

end JSQHalfinWhitt.Tightness.Supplement
