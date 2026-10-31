-- Prove2me | Theorems.Thm_FuchsThesis_Types_theorem_2_5
-- name    : FuchsThesis.Types.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:45.006986+00:00
-- url     : https://prove2.me/theorems/cc690b9e-3111-4b0f-85de-fab20e256245
-- title:
--   Theorem 2.5: $P(\vec b)=e^{-n[H(p_1)+K(p_1/p_0)]}$ on the class $T(p_1)$
-- statement:
--   Let $p_0$ be a probability distribution on $\{1,\dots,B\}$ and let $\vec b$ be a string of length $n$ with empirical frequency distribution $p_1$. Then the probability of $\vec b$ depends on $\vec b$ only through $p_1$:
--
--   $$
--   P(\vec b)=e^{-n[H(p_1)+K(p_1/p_0)]},
--   $$
--
--   where $H(p_1)=-\sum_b p_1(b)\ln p_1(b)$ and $K(p_1/p_0)=\sum_b p_1(b)\ln\frac{p_1(b)}{p_0(b)}$. If $p_0(b)=0<p_1(b)$ for some $b$, then $K(p_1/p_0)=+\infty$ and the formula reads $P(\vec b)=0$.
--
--   All strings with the same frequencies are equally likely, and the exponent separates into an entropy term and a relative-information term.
--
--   **Formalization Note** The relative information is the real-valued `kl`, in which $\ln(x/0)$ is $0$ rather than $+\infty$. The statement has two clauses: the formula when $p_1(b)>0$ implies $p_0(b)>0$ for every $b$, and $P(\vec b)=0$ otherwise. As $p_0\ge0$, the clauses cover every case.
--
--   Differences from the source:
--   - encoding: P(b) = e^{-n[H+K]} with K = +∞ allowed when p0(b) = 0 < p1(b) → two clauses, the real formula under `∀ b, 0 < p1 b → 0 < p0 b` and `wordProb p0 n s = 0` otherwise; reason: `Real.log (x / 0)` is 0 in Lean, and the clauses are exhaustive, so no instance is lost.
--   - encoding: the experiment is repeated n times and (2.77) divides by n → `1 ≤ n`; reason: excludes the undefined case n = 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Theorem 2.5, p.27

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_FuchsThesis_Types_entropy

set_option autoImplicit false

open ModernOnlineLearning.Portfolio GraphAlignment.Impossible HolevoCQ

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Theorem 2.5, (2.91) with (2.92), p.27 (PDF 36): for a string `s ∈ T(p1)`,
`P(s) = exp(-n [H(p1) + K(p1/p0)])`.

**Formalization Note.** `K(p1/p0)` is `kl p1 p0` from (2.76), a real number. When `p0 b = 0 < p1 b`
for some `b`, the source's `K(p1/p0)` is `+∞` and (2.91) reads `P(s) = 0`, but `Real.log (x / 0)` is
the junk value `0`; the statement therefore has two clauses: the real formula when `p1` is supported
where `p0` is, and `P(s) = 0` in the remaining case. Since `p0 ≥ 0`, the two clauses are exhaustive.
A term with `p1 b = 0` contributes `0` to both `H` and `K`, also when `p0 b = 0`. -/
theorem theorem_2_5 {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ stdSimplex ℝ (Fin B))
    (p1 : Fin B → ℝ) (s : Fin n → Fin B) (hs : s ∈ typeClass (T := n) p1) :
    ((∀ b, 0 < p1 b → 0 < p0 b) →
      wordProb p0 n s = Real.exp (-(n : ℝ) * (entropy p1 + kl p1 p0))) ∧
    ((∃ b, 0 < p1 b ∧ p0 b = 0) → wordProb p0 n s = 0) := by sorry

end FuchsThesis.Types
