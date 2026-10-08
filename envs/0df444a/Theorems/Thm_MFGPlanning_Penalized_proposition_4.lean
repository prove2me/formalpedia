-- Prove2me | Theorems.Thm_MFGPlanning_Penalized_proposition_4
-- name    : MFGPlanning.Penalized.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:59:54.541757+00:00
-- url     : https://prove2.me/theorems/fa62b2bf-0b71-4b3e-91e6-47079bbfed16
-- title:
--   Proposition 4 — solutions of the penalized scheme converge to a solution of the planning scheme as $\varepsilon \to 0$
-- statement:
--   Assume the hypotheses of Theorem 1: $g$ satisfies (G1), (G3), (G4), (G5); $W$ satisfies (24); $m_0, m_T \in \mathcal K$ with $(m_0)_{i,j} > 0$ for all $(i,j)$; and either $\nu > 0$, or $\nu = 0$ and $(m_T)_{i,j} > 0$ for all $(i,j)$.
--
--   1. Let $\varepsilon_k > 0$ with $\varepsilon_k \to 0$, let $(U^{\varepsilon_k}, M^{\varepsilon_k})$ solve the penalized scheme (20)–(23), and let $(M^n)_{0 \le n \le N_T}$ be grid functions in $\mathcal K$ with
--   $$
--   \lim_{k\to\infty} \max_n \|M^{\varepsilon_k,n} - M^n\|_\infty = 0.
--   $$
--   Then there are grid functions $(U^n)$ and a further subsequence along which $\max_n \|U^{\varepsilon_k,n} - U^n\|_\infty \to 0$, and $(U^n, M^n)_n$ solves the planning scheme (43)–(46).
--   2. If moreover $q \mapsto g(x_{i,j}, q)$ is strictly convex at every grid point, then (43)–(46) has a unique solution $(\bar U, \bar M)$ with $\sum_{i,j}\bar U^0_{i,j} = 0$, and for every $\varepsilon_k > 0$ with $\varepsilon_k \to 0$ and every choice of solutions of (20)–(23), the whole sequence converges:
--   $$
--   \lim_{k\to\infty}\max_n\Big(\|U^{\varepsilon_k,n} - \bar U^n\|_\infty + \|M^{\varepsilon_k,n} - \bar M^n\|_\infty\Big) = 0.
--   $$
--
--   The proposition justifies the penalized scheme as a numerical method for the discrete planning problem: its solutions, which exist and are unique for each $\varepsilon > 0$, approximate a solution of (18).
--
--   **Formalization Note** Convergence in the product topology on the finite-dimensional space of families of grid functions is exactly $\max_n\|\cdot\|_\infty$-convergence. "A subsequence still called $\varepsilon$" is covered by quantifying over every positive sequence $\varepsilon_k \to 0$. Solutions of (43)–(46) are unique only up to an additive constant in $U$, so "the unique solution" is the one with $\sum_{i,j} U^0_{i,j} = 0$; every limit of penalized solutions has this normalization, since $U^{\varepsilon,0} = (M^{\varepsilon,0} - m_0)/\varepsilon$ with $M^{\varepsilon,0}, m_0 \in \mathcal K$. In part 2 the convergence of $M^{\varepsilon_k}$ is not assumed. (G2) is not encoded.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.2, Proposition 4, p. 16

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme

namespace MFGPlanning.Penalized

open Filter Topology

/-- Proposition 4, hal-00465404v1, §3.2, p. 16 (PDF 17). Under the assumptions of Theorem 1:
(a) for every sequence ε_k → 0 with ε_k > 0, solutions (U^{ε_k}, M^{ε_k}) of (20)–(23) and grid
functions M^n ∈ K with max_n ‖M^{ε_k,n} − M^n‖_∞ → 0, there are grid functions (U^n) and a
further subsequence along which max_n ‖U^{ε,n} − U^n‖_∞ → 0, and (U^n, M^n) solves (43)–(46);
(b) if g is strictly convex, the whole sequence (U^{ε_k,n}, M^{ε_k,n}) converges to the unique
solution of (43)–(46) normalized by Σ_{i,j} U^0_{i,j} = 0.
Formalization Note: convergence in the product topology on the finite-dimensional space
`Fin (NT+1) → Pt → ℝ` is exactly max_n ‖· − ·‖_∞ → 0. "A subsequence still called ε" is covered
by quantifying over every positive sequence ε_k → 0. Solutions of (43)–(46) are unique only up to
an additive constant in U, so "the unique solution" is the one with Σ U^0 = 0, a normalization
every limit of penalized solutions satisfies (U^{ε,0} = (M^{ε,0} − m_0)/ε with M^{ε,0}, m_0 ∈ K).
In (b) the convergence of M along the sequence is not assumed. -/
theorem proposition_4 (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ) (Mbar : Fin (d.NT + 1) → Pt d → ℝ),
      (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
      (∀ n, InK d (Mbar n)) → Tendsto M atTop (𝓝 Mbar) →
      ∃ (Ubar : Fin (d.NT + 1) → Pt d → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (U ∘ φ) atTop (𝓝 Ubar) ∧ IsPlanningSol d Ubar Mbar) ∧
    ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) →
      ∃ Ubar Mbar : Fin (d.NT + 1) → Pt d → ℝ,
        (IsPlanningSol d Ubar Mbar ∧ ∑ p, Ubar 0 p = 0) ∧
        (∀ U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U' M' → ∑ p, U' 0 p = 0 →
          U' = Ubar ∧ M' = Mbar) ∧
        (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ),
          (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
          (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
          Tendsto (fun k => (U k, M k)) atTop (𝓝 (Ubar, Mbar)))) := by sorry

end MFGPlanning.Penalized
