-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_theorem_2_4_i
-- name    : ModelFreeBounds.Duality.theorem_2_4_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:49.703464+00:00
-- url     : https://prove2.me/theorems/b4ee590d-e21b-4bba-8804-3677b8769d16
-- title:
--   Theorem 2.4(i), p. 6 — under Assumption 2.1 the superhedging price ϕ(f) is > −∞
-- statement:
--   Let $\Omega$ be a nonempty Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$ satisfying the no-arbitrage Assumption 2.1. Let $f:\Omega\to\mathbb R$ be Borel measurable and let
--   $$\phi(f)=\inf\{c+\pi(y):c\in\mathbb R,\ y\in\mathbb R^m,\ c+\langle y,g\rangle\ge f\}.$$
--   Then
--   $$\phi(f)>-\infty .$$
--
--   This is the first part of the superhedging duality theorem: no-arbitrage rules out superhedging $f$ at arbitrarily negative cost.
--
--   **Formalization Note** $\phi(f)$ takes values in `EReal`. The hypothesis that $\Omega$ is nonempty is added: for $\Omega=\emptyset$ every $(c,y)$ is feasible and $\phi(f)=-\infty$. The paper's examples ($\Omega=\mathbb R^d_+$) are nonempty, and the paper tacitly assumes this.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Theorem 2.4(i), p. 6

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem theorem_2_4_i {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [Nonempty Ω] {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) :
    ⊥ < M.superhedgingPrice f := by sorry

end ModelFreeBounds.Duality
