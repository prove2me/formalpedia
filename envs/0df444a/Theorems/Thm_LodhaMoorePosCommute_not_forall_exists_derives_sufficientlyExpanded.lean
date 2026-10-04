-- Prove2me | Theorems.Thm_LodhaMoorePosCommute_not_forall_exists_derives_sufficientlyExpanded
-- name    : LodhaMoorePosCommute.not_forall_exists_derives_sufficientlyExpanded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T19:32:59.764711+00:00
-- url     : https://prove2.me/theorems/b2454ba6-4adc-4e33-9abf-a48b1a234e53
-- title:
--   Lodha–Moore Lemma 5.6 fails when the commutation rule moves only positive letters
-- statement:
--   Read with the substitutions of `LodhaMoorePosCommute.Step`, Lemma 5.6 of Lodha and Moore (p. 11: "If $\Omega$ is a standard form, then there is a sufficiently expanded standard form which can be derived from $\Omega$") is false. `LodhaMoorePosCommute.Step` is the Lodha–Moore mission's substitution relation with the commutation $y_u y_v \Leftrightarrow y_v y_u$ applied only to letters with positive exponents. The statement says that not every standard form (`LodhaMoore.IsStandardForm`) derives a sufficiently expanded standard form (`LodhaMoore.SufficientlyExpanded`) by finitely many such substitutions.
--
--   The proof of Lemma 5.6 moves letters with negative exponents by this substitution: "We may therefore apply substitution of the form $y_u y_v \Leftrightarrow y_v y_u$ for incompatible $u$ and $v$ in order to move any two distinct occurrences of $y_{s0}$, $y_{s10}$, or $y_{s11}$ to the same position" (p. 11). The letter $y_{s10}$ there has exponent $-1$, so the printed rule, which carries no exponents, must be read with arbitrary exponents. The Lodha–Moore mission reads it that way (`LodhaMoore.Step`).
--
--   The counterexample is the standard form $\Omega = y_{00}^{-1}\, y_{01}^{-1}\, y_1^{-1}\, y_\varnothing$, where $\varnothing$ is the empty sequence. It is not sufficiently expanded: $\varnothing$ is not exposed and $y_0$ does not occur. Under the restricted rule, no word derived from $\Omega$ ever has two adjacent positive $y$-letters or two adjacent $y$-letters with the same subscript. So commutation, cancellation and merging of $y$-letters never apply, and no derived standard form is sufficiently expanded. With arbitrary exponents, $\Omega$ derives $x_\varnothing\, y_{10}^{-2}$, which is sufficiently expanded.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 9, the substitution yᵤyᵥ ⇔ yᵥyᵤ read for positive exponents, and p. 11, Lemma 5.6

import Definitions.Def_LodhaMoorePosCommute
import Definitions.Def_LodhaMooreWords
import Mathlib

namespace LodhaMoorePosCommute

theorem not_forall_exists_derives_sufficientlyExpanded :
    ¬ ∀ Ω : LodhaMoore.Word, LodhaMoore.IsStandardForm Ω →
      ∃ Ω', Relation.ReflTransGen Step Ω Ω' ∧ LodhaMoore.IsStandardForm Ω' ∧
        LodhaMoore.SufficientlyExpanded Ω' := by
  sorry

end LodhaMoorePosCommute
