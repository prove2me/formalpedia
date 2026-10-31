-- Prove2me | Theorems.Thm_FuchsThesis_Types_theorem_2_6
-- name    : FuchsThesis.Types.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:00.46204+00:00
-- url     : https://prove2.me/theorems/bae7ed86-ad7e-4a37-85e3-b7414186d15f
-- title:
--   Theorem 2.6: $(n+1)^{-B}e^{-nK(p_1/p_0)}\le P(T(p_1))\le e^{-nK(p_1/p_0)}$
-- statement:
--   An experiment with $B$ outcomes and single-trial probability distribution $p_0$ is repeated $n$ times. Let $p_1\in\mathcal F$ be an empirical frequency distribution of strings of length $n$, and let $T(p_1)$ be the set of strings with those frequencies. Then
--
--   $$
--   (n+1)^{-B}e^{-nK(p_1/p_0)}\le P(T(p_1))\le e^{-nK(p_1/p_0)},
--   $$
--
--   where $K(p_1/p_0)=\sum_b p_1(b)\ln\frac{p_1(b)}{p_0(b)}$ is the Kullback–Leibler relative information. If $p_0(b)=0<p_1(b)$ for some $b$, then $K(p_1/p_0)=+\infty$ and the statement reads $P(T(p_1))=0$.
--
--   The relative information is therefore the exponential rate at which the probability of an "incorrect" frequency goes to zero, which gives it an operational meaning.
--
--   **Formalization Note** The relative information is the real-valued `kl`, in which $\ln(x/0)$ is $0$ rather than $+\infty$. The statement has two clauses: the real bounds when $p_1(b)>0$ implies $p_0(b)>0$ for every $b$, and $P(T(p_1))=0$ otherwise. As $p_0\ge0$, the clauses cover every case, so $p_0$ may vanish.
--
--   Differences from the source:
--   - encoding: (2.98) with K = +∞ allowed when p0(b) = 0 < p1(b) → two clauses, the real bounds under `∀ b, 0 < p1 b → 0 < p0 b` and `P(T(p1)) = 0` otherwise; reason: `Real.log (x / 0)` is 0 in Lean, and the clauses are exhaustive, so no instance is lost.
--   - encoding: p1 is called a frequency distribution in n trials → `p1 ∈ possibleTypes B n`; reason: for any other p1 the class is empty and the frequency distribution does not exist.
--   - encoding: the experiment is repeated n times and (2.77) divides by n → `1 ≤ n`; reason: excludes the undefined case n = 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.6, p.29

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures
import Definitions.Def_FuchsThesis_Types_probEvent

set_option autoImplicit false

open ModernOnlineLearning.Portfolio GraphAlignment.Impossible

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.6, (2.98), p.29 (PDF 38): for a single-trial distribution `p0`
and a frequency distribution `p1 ∈ F` of strings of length `n` over `B` outcomes,
`(n + 1)^(-B) exp(-n K(p1/p0)) ≤ P(T(p1)) ≤ exp(-n K(p1/p0))`.

**Formalization Note.** `K(p1/p0)` is `kl p1 p0` from (2.76), a real number. When `p0 b = 0 < p1 b`
for some `b`, the source's `K(p1/p0)` is `+∞` and (2.98) reads `0 ≤ P(T(p1)) ≤ 0`, but
`Real.log (x / 0)` is the junk value `0`; the statement therefore has two clauses: the real bounds
when `p1` is supported where `p0` is, and `P(T(p1)) = 0` in the remaining case. Since `p0 ≥ 0`, the
two clauses are exhaustive, so the theorem covers every `p0`, zeros included. `p1 ∈ F` is the source's
"frequency distribution": for `p1 ∉ F` the class `T(p1)` is empty and the lower bound fails. `n ≥ 1`
is the source's setting, in which (2.77) is defined. -/
theorem theorem_2_6 {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ stdSimplex ℝ (Fin B))
    (p1 : Fin B → ℝ) (hp1 : p1 ∈ possibleTypes B n) :
    ((∀ b, 0 < p1 b → 0 < p0 b) →
      ((n : ℝ) + 1) ^ (-(B : ℤ)) * Real.exp (-(n : ℝ) * kl p1 p0) ≤
          probEvent p0 (typeClass (T := n) p1) ∧
        probEvent p0 (typeClass (T := n) p1) ≤ Real.exp (-(n : ℝ) * kl p1 p0)) ∧
    ((∃ b, 0 < p1 b ∧ p0 b = 0) → probEvent p0 (typeClass (T := n) p1) = 0) := by sorry

end FuchsThesis.Types
