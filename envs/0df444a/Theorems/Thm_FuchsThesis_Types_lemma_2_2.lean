-- Prove2me | Theorems.Thm_FuchsThesis_Types_lemma_2_2
-- name    : FuchsThesis.Types.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:41.199101+00:00
-- url     : https://prove2.me/theorems/55e8a723-b22a-4421-b5de-7eceaf803a14
-- title:
--   Lemma 2.2: $(n+1)^{-B}e^{nH(p_1)}\le|T(p_1)|\le e^{nH(p_1)}$
-- statement:
--   For every empirical frequency distribution $p_1\in\mathcal F$ of strings of length $n$ over $B$ outcomes, the type class $T(p_1)$ satisfies
--
--   $$
--   (n+1)^{-B}e^{nH(p_1)}\le|T(p_1)|\le e^{nH(p_1)}.
--   $$
--
--   The size of a type class is thus $e^{nH(p_1)}$ up to a factor polynomial in $n$. This estimate links the relative information to the probability of an incorrect frequency.
--
--   Differences from the source:
--   - encoding: the experiment is repeated n times and (2.77) divides by n → `1 ≤ n`; reason: excludes the undefined case n = 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Lemma 2.2, p.28

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_FuchsThesis_Types_entropy

set_option autoImplicit false

open ModernOnlineLearning.Portfolio

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Lemma 2.2, (2.95), p.28 (PDF 37): for every `p1 ∈ F`,
`(n + 1)^(-B) exp(n H(p1)) ≤ |T(p1)| ≤ exp(n H(p1))`.

**Formalization Note.** `B` is the number of outcomes (`Fin B`) and `n` the string length, as in the
source. `n ≥ 1` is the source's setting, in which (2.77) is defined. -/
theorem lemma_2_2 {B n : ℕ} (hn : 1 ≤ n) (p1 : Fin B → ℝ) (hp1 : p1 ∈ possibleTypes B n) :
    ((n : ℝ) + 1) ^ (-(B : ℤ)) * Real.exp ((n : ℝ) * entropy p1) ≤
        ((typeClass (T := n) p1).card : ℝ) ∧
      ((typeClass (T := n) p1).card : ℝ) ≤ Real.exp ((n : ℝ) * entropy p1) := by sorry

end FuchsThesis.Types
