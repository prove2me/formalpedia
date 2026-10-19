-- Prove2me | Theorems.Thm_OAI_SpinAngle_EntropyMonomial_sum_log_ratio
-- name    : OAI.SpinAngle.EntropyMonomial.sum_log_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:13:37.48299+00:00
-- url     : https://prove2.me/theorems/8eb10d4c-f445-40a2-9110-5af41b4c4ccd
-- title:
--   Entropy of a count vector as $-\sum_i n_i\log(n_i/p)$
-- statement:
--   Let $\iota$ be a finite index set and let $n=(n_i)_{i\in\iota}$ be a family of nonnegative integers with total $N=\sum_{i\in\iota}n_i$. The *entropy* of $n$ is
--   $$H(n)=N\log N-\sum_{i\in\iota}n_i\log n_i ,$$
--   with the convention $0\log0=0$.
--
--   **Theorem.** If $p$ is a positive integer with $\sum_{i\in\iota}n_i=p$, then
--   $$\sum_{i\in\iota}n_i\log\frac{n_i}{p}=-H(n).$$
--
--   Equivalently, $H(n)=p\sum_i\big(-\tfrac{n_i}{p}\log\tfrac{n_i}{p}\big)$ is $p$ times the Shannon entropy (in nats) of the empirical distribution $(n_i/p)_{i\in\iota}$, and exponentiating gives $\prod_i(n_i/p)^{n_i}=e^{-H(n)}$. This is the form in which the entropy of the row lengths of a Young-diagram type is compared with monomials $\prod_it_i^{n_i}$ in the eigenvalues of a density matrix.
--
--   **Formalization Note** The entropy is `EntropyMonomial.entropy n`. Since `Real.log 0 = 0` in Lean, the terms with $n_i=0$ vanish on both sides, which realizes the convention $0\log0=0$; the hypothesis $p>0$ is what allows $\log(n_i/p)=\log n_i-\log p$ for $n_i\ne0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean#L2122-L2134

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle OAI.SpinAngle.EntropyMonomial
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
variable {ι : Type*} [contextInstance2001_21 : Fintype ι]

theorem OAI.SpinAngle.EntropyMonomial.sum_log_ratio (n : ι → ℕ) (p : ℕ) (hp : 0 < p) (hn : ∑ i, n i = p) :
    ∑ i, (n i : ℝ) * Real.log ((n i : ℝ) / p) = -entropy n := by sorry
