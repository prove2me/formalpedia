-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_pooled_mass
-- name    : OAI.DiamondDistortion.FiniteAverage.pooled_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:36:32.797995+00:00
-- url     : https://prove2.me/theorems/4f4d3e7f-91cc-476a-815d-e536755d7a17
-- title:
--   Averaged opposite-sign cancellation bound for pooled absolute masses
-- statement:
--   Let $\Omega$ and $\kappa$ be finite sets and let $w:\Omega\to\mathbb{R}$ be probability weights ($w(\omega)\ge0$ for all $\omega$ and $\sum_{\omega}w(\omega)=1$). Let $b,W:\Omega\times\kappa\to\mathbb{R}$ and $V,L:\Omega\to\mathbb{R}$ be arbitrary real functions, written $b_\omega(g)$, $W_\omega(g)$, $V_\omega$, $L_\omega$. Assume:
--
--   1. (the mean of $b$ is cancelled by $W$) for every $g\in\kappa$, $\sum_{\omega}w(\omega)\,b_\omega(g)=-\sum_\omega w(\omega)\,W_\omega(g)$;
--   2. (energy of $W$) for every $\omega\in\Omega$, $\sum_{g\in\kappa}W_\omega(g)^2\le V_\omega$;
--   3. (opposite-sign budget) for all $\omega,\nu\in\Omega$, $\sum_{g\in\kappa}\big(|b_\omega(g)|\,|b_\nu(g)|-b_\omega(g)\,b_\nu(g)\big)\le L_\omega+L_\nu$.
--
--   Then
--   $$
--   \sum_{g\in\kappa}\Big(\sum_{\omega\in\Omega}w(\omega)\,|b_\omega(g)|\Big)^2\le\sum_{\omega\in\Omega}w(\omega)V_\omega+2\sum_{\omega\in\Omega}w(\omega)L_\omega .
--   $$
--
--   The left side is the squared Euclidean norm of the pooled absolute masses $g\mapsto\sum_\omega w(\omega)|b_\omega(g)|$. The quantity $|b_\omega(g)||b_\nu(g)|-b_\omega(g)b_\nu(g)$ vanishes unless $b_\omega(g)$ and $b_\nu(g)$ have strictly opposite signs, so hypothesis 3 measures how much the coefficient vectors of different outcomes cancel against each other; together with the control of the signed mean through the error term $W$, this bounds the pooled absolute mass. It is a purely finite averaging inequality, used to control averaged opposite-sign cancellation together with the energy of an error term.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean#L69-L125

import Mathlib
import Definitions.Def_DiamondDistortion

open OAI OAI.DiamondDistortion
universe u v
open scoped BigOperators Classical Topology
open Set
variable {Ω : Type*} [Fintype Ω]

theorem OAI.DiamondDistortion.FiniteAverage.pooled_mass {κ : Type*} [Fintype κ]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (b W : Ω → κ → ℝ) (V L : Ω → ℝ)
    (hmean : ∀ g, (∑ ω,w ω*b ω g) = -(∑ ω,w ω*W ω g))
    (hW : ∀ ω, (∑ g,W ω g ^ 2) ≤ V ω)
    (hopp : ∀ ω ν, (∑ g, (|b ω g| * |b ν g| - b ω g*b ν g)) ≤ L ω + L ν) :
    (∑ g, (∑ ω,w ω* |b ω g|)^2) ≤ (∑ ω,w ω*V ω) + 2*(∑ ω,w ω*L ω) := by sorry
