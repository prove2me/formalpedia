-- Prove2me | Theorems.Thm_GaussProcSparsify_Optimal_theorem_1
-- name    : GaussProcSparsify.Optimal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:37.719609+00:00
-- url     : https://prove2.me/theorems/52f7fe16-2f00-4de2-bf52-61bf317deb7d
-- title:
--   Theorem 1 — Optimal dimension-free sparsification of Gaussian processes
-- statement:
--   There is a universal constant $C>0$ such that the following holds for every dimension $n$, every nonempty bounded set $T\subseteq\mathbb R^n$, and every $\varepsilon>0$. There are a finite nonempty set $S\subseteq T$ and nonnegative real constants $(c_s)_{s\in S}$ satisfying
--   $$|S|\le\exp(C/\varepsilon^2),\qquad\left\|\sup_{t\in T}\langle g,t\rangle-\max_{s\in S}\{\langle g,s\rangle+c_s\}\right\|_{L^2(\gamma_n)}\le\varepsilon\,w(T).$$
--   The constant is chosen before $n,T,\varepsilon$, and is independent of all three. The set and shifts are deterministic, chosen before the Gaussian input $g$. The statement includes uncountable bounded sets, dimension zero, singleton sets, and arbitrary positive accuracy parameters. There is no restriction $\varepsilon<1$.
--
--   This is the paper's full sparsification theorem: both subset containment and nonnegativity of the shifts are essential parts of the conclusion.
--
--   Differences from the source:
--   - encoding: a bounded set $T$ and a maximum over $S$ → $T$ and the finite set $S$ are explicitly nonempty; reason: empty suprema and maxima are undefined in the source; no defined instance is excluded
--   - encoding: $\mathbb R^n$ with the Euclidean norm and standard Gaussian law → `EuclideanSpace ℝ (Fin n)` and `stdGaussian`, including $n=0$; reason: these give the same inner product, norm and Gaussian distribution
--   - encoding: $\exp(O(1/\varepsilon^2))$ → $\exists C>0$ before all $n,T,\varepsilon$, with $|S|\le\exp(C/\varepsilon^2)$; reason: this states the universal upper-bound constant in the printed big-O notation explicitly
--   - encoding: Gaussian width and $L^2$ error → extended-real finite-marginal width, converted to real only for bounded nonempty $T$, and `eLpNorm` for error; reason: the width is finite on exactly this domain and agrees with the expected supremum, while the extended norm avoids any integrability default
--   - encoding: shifts indexed by $s\in S$ → an ambient real function $c$ restricted to $S$; reason: every finite family extends to such a function, and values outside $S$ are never used
--   - encoding: $\sup_{t\in T}g\cdot t$ → `processSup T g`, the real `sSup` of the image of $T$; reason: for nonempty bounded $T$ the image is nonempty and bounded above, so this is the true supremum
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), Theorem 1, PDF p. 3 (printed p. 2), restated PDF p. 18 (printed p. 17), proved PDF pp. 18–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_GaussProcSparsify_Optimal_Gaussian

open MeasureTheory

namespace GaussProcSparsify.Optimal

/-- Theorem 1, PDF p. 3 (restated p. 18). A single C works in every dimension,
for every bounded nonempty T, including uncountable sets, and every ε > 0. -/
theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T : Set (Vec n)), T.Nonempty →
      Bornology.IsBounded T → ∀ ε : ℝ, 0 < ε →
      ∃ (S : Finset (Vec n)) (hS : S.Nonempty) (c : Vec n → ℝ),
        (↑S : Set (Vec n)) ⊆ T ∧ (∀ s ∈ S, 0 ≤ c s) ∧
        (S.card : ℝ) ≤ Real.exp (C / ε ^ 2) ∧
        eLpNorm (fun g => processSup T g - shiftedMax S hS c g) 2 (gaussian n) ≤
          ENNReal.ofReal (ε * (gaussianWidth T).toReal) := by sorry

end GaussProcSparsify.Optimal
