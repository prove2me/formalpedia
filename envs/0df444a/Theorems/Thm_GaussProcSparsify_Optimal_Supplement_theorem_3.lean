-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_Supplement_theorem_3
-- name    : GaussProcSparsify.Optimal.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:23:18.233181+00:00
-- url     : https://prove2.me/theorems/908ec5de-dd85-4b84-b711-b7c9bc950b21
-- title:
--   Theorem 3 — junta approximation of every norm
-- statement:
--   There is a universal constant $C>0$ such that, for every $0<\varepsilon<1/2$ and every norm $\psi$ on Euclidean $\mathbb R^n$, some $k$-junta norm $\varphi$ satisfies
--   $$k\le\exp\left(C\frac{\log(1/\varepsilon)}{\varepsilon^4}\right),\qquad\Pr_{\gamma_n}[(1-\varepsilon)\varphi(g)\le\psi(g)\le(1+\varepsilon)\varphi(g)]\ge1-\varepsilon.$$
--   For $n>0$, the chosen $\varphi$ is positive almost everywhere and the displayed event agrees almost everywhere with the paper's event $1-\varepsilon\le\psi(g)/\varphi(g)\le1+\varepsilon$. Junta dependence is through an arbitrary subspace, on which the defining norm is genuine. This companion theorem describes multiplicative approximation by a function of few linear directions.
--
--   Differences from the source:
--   - encoding: Euclidean R^n → EuclideanSpace ℝ (Fin n); reason: the fixed Euclidean coordinates, inner product and standard Gaussian law are preserved
--   - encoding: universal constants in asymptotic notation → positive existential constants before all instance parameters; reason: spells out the uniformity of the source bounds without selecting a numerical constant
--   - encoding: an arbitrary norm ψ → a real Seminorm with trivial kernel; reason: this is exactly definiteness, absolute homogeneity and subadditivity, without changing the ambient Gaussian structure
--   - encoding: the ratio event with ψ/φ → the crossed inequalities together with almost-everywhere positivity and ratio equivalence when n>0; reason: division is used only where the denominator is positive, preserving every positive-dimensional instance
--   - generalization: the printed ratio is undefined at n=0 because ψ=φ=0 → the crossed event is the whole zero-dimensional space and the ratio-equivalence clause is required only for n>0; reason: adds the trivial zero-dimensional case while retaining the entire printed claim whenever its ratio is defined
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Theorem 3, PDF p. 4–5 (printed p. 3–4), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Definitions.Def_GaussProcSparsify_Optimal_Supplement_Junta

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal.Supplement

/-- Theorem 3, PDF pp. 4–5 (restatement p. 24). The crossed event avoids 0/0.
For positive n the chosen junta norm is positive almost everywhere, so division
recovers exactly the printed ratio ψ/φ. At n=0 the crossed event is the whole space. -/
theorem theorem_3 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ε : ℝ) (ψ : Seminorm ℝ (Vec n)), 0 < ε → ε < 1 / 2 →
      (∀ x : Vec n, ψ x = 0 → x = 0) →
      ∃ (k : ℕ) (φ : Vec n → ℝ), IsJuntaNorm k φ ∧
        (k : ℝ) ≤ Real.exp (C * Real.log (1 / ε) / ε ^ 4) ∧
        ENNReal.ofReal (1 - ε) ≤ gaussian n
          {g | (1 - ε) * φ g ≤ ψ g ∧ ψ g ≤ (1 + ε) * φ g} ∧
        (0 < n → ∀ᵐ g ∂gaussian n, 0 < φ g ∧
          (((1 - ε) * φ g ≤ ψ g ∧ ψ g ≤ (1 + ε) * φ g) ↔
            (1 - ε ≤ ψ g / φ g ∧ ψ g / φ g ≤ 1 + ε))) := by sorry

end GaussProcSparsify.Optimal.Supplement
