-- Prove2me | Theorems.Thm_FunctionalIto_Formula_lemma_A_1
-- name    : FunctionalIto.Formula.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:39.694011+00:00
-- url     : https://prove2.me/theorems/d10ee308-d56d-4528-b136-a49fa7242de5
-- title:
--   Lemma A.1, p. 21 — a cadlag function is uniformly continuous up to its jumps (61)
-- statement:
--   Let $f$ be a cadlag function on $[0,T]$ with values in a normed group, and write $\Delta f(t)=f(t)-f(t-)$ for its jump at $t$. Then for every $\varepsilon>0$ there is $\eta>0$ such that, for all $0\le x\le y\le T$ with $y-x\le\eta$,
--   $$\|f(x)-f(y)\|\le\varepsilon+\sup_{t\in(x,y]}\|\Delta f(t)\|.$$
--
--   A cadlag function is not uniformly continuous, but its increments over short intervals are controlled by its largest jump inside the interval. This is the tool behind the step-function approximation (Lemma A.3) and the stopping-time lemma (Lemma A.2).
--
--   **Formalization Note.** The supremum is replaced by its upper bounds: the conclusion holds for every $s\ge0$ that bounds $\|\Delta f(t)\|$ on $(x,y]$, which is equivalent and assigns the empty interval the value $0$. The paper's $|x-y|\le\eta$ is stated with $x\le y$, which loses nothing by symmetry. Left limits are Mathlib's `Function.leftLim`.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 21, Lemma A.1, (61)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Lemma A.1 (p. 21), (61): a cadlag function on `[0,T]` is uniformly continuous up to its
jumps. With `Δf(t) = f(t) − f(t−)`: for every `ε > 0` there is `η > 0` such that
`x ≤ y ≤ T`, `y − x ≤ η` imply `‖f(x) − f(y)‖ ≤ ε + sup_{t ∈ (x,y]} ‖Δf(t)‖`.
The supremum (taken to be `0` on an empty interval) is encoded by its upper bounds `s ≥ 0`. -/
theorem lemma_A_1 {E : Type*} [NormedAddCommGroup E] (T : ℝ≥0) (f : ℝ≥0 → E)
    (hf : CadlagOn T f) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ x y : ℝ≥0, x ≤ y → y ≤ T → (y : ℝ) - x ≤ η →
      ∀ s : ℝ, 0 ≤ s → (∀ t ∈ Set.Ioc x y, ‖f t - Function.leftLim f t‖ ≤ s) →
        ‖f x - f y‖ ≤ ε + s := by sorry

end FunctionalIto.Formula
