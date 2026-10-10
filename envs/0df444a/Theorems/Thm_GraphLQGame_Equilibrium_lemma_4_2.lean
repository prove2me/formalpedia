-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_lemma_4_2
-- name    : GraphLQGame.Equilibrium.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:28:05.612763+00:00
-- url     : https://prove2.me/theorems/a62261bb-83b6-411b-900f-20212763161d
-- title:
--   Lemma 4.2 — a quadratic solution of the Nash system (4.1) solves the Riccati system (4.6)–(4.7)
-- statement:
--   Let $G$ be transitive without isolated vertices, $L=L_G$, and $c,\sigma,T>0$. Suppose $v_i(t,x)=\frac12x^\top F^i(t)x+h_i(t)$ (4.5), with $F^i(t)$ symmetric, is a classical solution of the Nash system (4.1). Then for all $i$ and $t\in(0,T)$,
--   $$0=\dot F^i(t)-\sum_{j=1}^nF^j(t)e_je_j^\top F^i(t)-F^i(t)\sum_{j=1}^ne_je_j^\top F^j(t)+F^i(t)e_ie_i^\top F^i(t),\qquad 0=\dot h_i(t)+\frac{\sigma^2}{2}\mathrm{Tr}(F^i(t)),$$
--   and
--   $$F^i(T)=cLe_ie_i^\top L,\qquad h_i(T)=0 .$$
--
--   This reduces the Nash system to a coupled matrix Riccati system.
--
--   **Formalization Note** $\dot F^i$ is the entrywise derivative; the Nash system is solved classically on $(0,T)\times\mathbb R^n$ with the terminal condition at $T$. $T,\sigma,c>0$ are the paper's standing assumptions.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Lemma 4.2, p. 25

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_NashSystem

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, Lemma 4.2, p. 25. Let `G` be transitive without isolated
vertices. If `v_i(t, x) = ½ xᵀ Fⁱ(t) x + h_i(t)` (4.5), with each `Fⁱ(t)` symmetric, is a solution
of the Nash system (4.1), then for `t ∈ (0, T)` and every `i`
`0 = Ḟⁱ − Σ_j Fʲ e_j e_jᵀ Fⁱ − Fⁱ Σ_j e_j e_jᵀ Fʲ + Fⁱ e_i e_iᵀ Fⁱ`,
`0 = ḣ_i + (σ²/2) Tr(Fⁱ)`  (4.6),
and `Fⁱ(T) = c L e_i e_iᵀ L`, `h_i(T) = 0` (4.7).

Formalization Note: vertices are `Fin n`; `e_j e_jᵀ` is `Matrix.single j j 1`; `Ḟⁱ` is the
entrywise derivative; "solution of (4.1)" is a classical solution on `(0, T) × ℝⁿ` with the
terminal condition at `T` (`IsNashSystemSol`). `T, σ, c > 0` are the paper's standing
assumptions (§2.1). -/
theorem lemma_4_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) (c σ T : ℝ) (hc : 0 < c) (hσ : 0 < σ)
    (hTpos : 0 < T) (F : Fin n → ℝ → Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ → ℝ)
    (hsymm : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, (F i t).transpose = F i t)
    (hsol : IsNashSystemSol G c σ T (ansatz F h)) :
    (∀ i, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        riccatiRes F i t = 0 ∧ deriv (h i) t + σ ^ 2 / 2 * (F i t).trace = 0) ∧
      (∀ i, F i T = c • (lap G * Matrix.single i i 1 * lap G) ∧ h i T = 0) := by sorry

end GraphLQGame.Equilibrium
