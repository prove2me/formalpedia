-- Prove2me | Theorems.Thm_FuchsThesis_Types_corollary_2_1
-- name    : FuchsThesis.Types.corollary_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:34.807953+00:00
-- url     : https://prove2.me/theorems/0a6c45bb-6e09-47d0-a1e4-f88d53228e4c
-- title:
--   Corollary 2.1: $P(\vec b)=e^{-nH(p_0)}$ on the class $T(p_0)$
-- statement:
--   Let $p_0$ be a probability distribution on $\{1,\dots,B\}$ and let $\vec b$ be a string of length $n$ whose empirical frequency distribution is $p_0$ itself. Then
--
--   $$
--   P(\vec b)=e^{-nH(p_0)}.
--   $$
--
--   This is the case $p_1=p_0$ of Theorem 2.5, and it turns the probability of a type class into a statement about the size of the class.
--
--   Differences from the source:
--   - encoding: the experiment is repeated n times and (2.77) divides by n → `1 ≤ n`; reason: excludes the undefined case n = 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, Corollary 2.1, p.28

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_FuchsThesis_Types_entropy

set_option autoImplicit false

open ModernOnlineLearning.Portfolio HolevoCQ

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, Corollary 2.1, (2.94), p.28 (PDF 37): a string `s ∈ T(p0)`, whose
frequencies equal the single-trial distribution `p0`, has probability `P(s) = exp(-n H(p0))`.

**Formalization Note.** `n ≥ 1` is the source's setting, in which (2.77) is defined. -/
theorem corollary_2_1 {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ stdSimplex ℝ (Fin B))
    (s : Fin n → Fin B) (hs : s ∈ typeClass (T := n) p0) :
    wordProb p0 n s = Real.exp (-(n : ℝ) * entropy p0) := by sorry

end FuchsThesis.Types
