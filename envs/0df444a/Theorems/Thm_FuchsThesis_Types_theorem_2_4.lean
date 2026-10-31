-- Prove2me | Theorems.Thm_FuchsThesis_Types_theorem_2_4
-- name    : FuchsThesis.Types.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:56.810965+00:00
-- url     : https://prove2.me/theorems/13b828c4-8280-4499-bad1-e5c9f6962c56
-- title:
--   Theorem 2.4: the most likely frequency is the single-trial distribution
-- statement:
--   Suppose the single-trial distribution $p_0$ is an element of $\mathcal F$, that is, $p_0$ is the empirical frequency vector of some string of length $n$. Let $T(p)=\{\vec b\in\{1,\dots,B\}^n: F_{\vec b}=p\}$. Then, for every $p_1$,
--
--   $$
--   P(T(p_0))\ge P(T(p_1)).
--   $$
--
--   In $n$ trials the most likely frequency distribution is therefore the distribution of a single trial itself.
--
--   **Formalization Note** The vector $p_1$ is arbitrary. If $p_1\notin\mathcal F$, then $T(p_1)$ is empty and the right side is $0$. Membership in $\mathcal F$ already makes $p_0$ a probability distribution.
--
--   Differences from the source:
--   - encoding: the experiment is repeated n times and (2.77) divides by n → `1 ≤ n`; reason: excludes the undefined case n = 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.4, p.26

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_FuchsThesis_Types_probEvent

set_option autoImplicit false

open ModernOnlineLearning.Portfolio

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.4, (2.81), p.26 (PDF 35): if the single-trial distribution `p0`
is itself an element of `F` (a frequency vector of some string of length `n`), then
`P(T(p0)) ≥ P(T(p1))`, for every `p1`.

**Formalization Note.** `p1` is an arbitrary real function, as in the source, which puts no condition
on it; for `p1 ∉ F` the class `T(p1)` is empty and the right side is `0`. Being in `F` makes `p0` a
probability distribution for `n ≥ 1`, so no separate hypothesis is needed. -/
theorem theorem_2_4 {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ possibleTypes B n)
    (p1 : Fin B → ℝ) :
    probEvent p0 (typeClass (T := n) p1) ≤ probEvent p0 (typeClass (T := n) p0) := by sorry

end FuchsThesis.Types
