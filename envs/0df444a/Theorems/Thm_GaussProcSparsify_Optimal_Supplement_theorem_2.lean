-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_theorem_2
-- name    : GaussProcSparsify.Optimal.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:21:38.439205+00:00
-- url     : https://prove2.me/theorems/0ad9145e-14e4-4837-854e-1028300fa56a
-- title:
--   Theorem 2 — optimal lower bound with arbitrary real shifts
-- statement:
--   There are universal constants $c,\varepsilon_0>0$ such that, for every $0<\varepsilon<\varepsilon_0$, there is a dimension $n$ and a nonempty bounded set $T_\varepsilon\subseteq\mathbb R^n$ with Gaussian width exactly one. Every finite nonempty $S\subseteq T_\varepsilon$ and every collection of arbitrary real shifts $b_s$ obey
--   $$\left\|\sup_{t\in T_\varepsilon}\langle g,t\rangle-\max_{s\in S}\{\langle g,s\rangle+b_s\}\right\|_{L^2(\gamma_n)}\le\varepsilon\quad\Longrightarrow\quad |S|\ge\exp(c/\varepsilon^2).$$
--   This companion theorem establishes the optimal dependence on accuracy for the goal's sparsifier size, even when negative shifts are permitted.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: bounded T and finite S in expressions involving sup and max → T.Nonempty and S.Nonempty with S a Finset; reason: excludes only undefined empty suprema and maxima, without restricting T to be finite
--   - encoding: finite maxima and Gaussian L² norms → nonempty finite families and extended eLpNorm bounds; reason: maxima are defined on exactly their nonempty domains, and infinite error cannot become zero
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Theorem 2, PDF p. 4 (printed p. 3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Theorem 2, PDF p. 4 (restatement p. 31). Arbitrary real shifts. -/
theorem theorem_2 :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ n : ℕ, ∃ T : Set (Vec n), T.Nonempty ∧ Bornology.IsBounded T ∧
          gaussianWidth T = 1 ∧
          ∀ (S : Finset (Vec n)) (hS : S.Nonempty), (↑S : Set (Vec n)) ⊆ T →
            ∀ b : Vec n → ℝ,
              eLpNorm (fun g => processSup T g - shiftedMax S hS b g) 2 (gaussian n) ≤
                ENNReal.ofReal ε →
              Real.exp (c / ε ^ 2) ≤ (S.card : ℝ) := by sorry

end GaussProcSparsify.Optimal.Supplement
