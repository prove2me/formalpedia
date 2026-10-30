-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_lemma_2
-- name    : InfoNudge.Cutoff.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:39.250581+00:00
-- url     : https://prove2.me/theorems/c32dc83d-d586-490d-bab8-276f106b7ab5
-- title:
--   Lemma 2, p. 14 — the cutoff mechanism π*_γ of (10) uniquely minimizes the expected harm E[θπ(θ)] among mechanisms with E[π(θ)] = γ
-- statement:
--   Under the standing assumptions, let $\gamma\in[0,1]$ and let $\pi^*_\gamma$ be the cutoff mechanism (10), with $t_\gamma=\inf\{\theta:F(\theta)>\gamma\}$, $0/0=1$ and $\inf\emptyset=\infty$. Then $\pi^*_\gamma$ is a mechanism with $E[\pi^*_\gamma(\theta)]=\gamma$, and it is, up to a $P$-null set, the unique solution of
--   $$\min\{E[\theta\pi(\theta)]:E[\pi(\theta)]=\gamma\}.\qquad(9)$$
--   That is, for every measurable $\pi$ with values in $[0,1]$ and $E[\pi(\theta)]=\gamma$,
--   $$E[\theta\pi^*_\gamma(\theta)]\le E[\theta\pi(\theta)],$$
--   with equality if and only if $\pi=\pi^*_\gamma$ $P$-almost surely.
--
--   The prior may be discrete, continuous or mixed; randomization occurs only at an atom $t_\gamma$. This "bathtub" lemma is the first step in the reduction of the design problem to cutoff mechanisms.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 14, Lemma 2, eqs. (9)–(10)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem lemma_2 (M : Params) (hS : Standing M) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    IsMechanism (cutoffMech M γ) ∧ (∫ θ, cutoffMech M γ θ ∂M.P) = γ ∧
    ∀ π : ℝ → ℝ, IsMechanism π → (∫ θ, π θ ∂M.P) = γ →
      (∫ θ, θ * cutoffMech M γ θ ∂M.P) ≤ ∫ θ, θ * π θ ∂M.P ∧
      ((∫ θ, θ * π θ ∂M.P) = ∫ θ, θ * cutoffMech M γ θ ∂M.P ↔
        π =ᵐ[M.P] cutoffMech M γ) := by sorry

end InfoNudge.Cutoff
