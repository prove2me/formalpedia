-- Prove2me | Theorems.Thm_Garrido_satisfiesFoelnerCondition_iff_hasFoelnerSequence
-- name    : Garrido.satisfiesFoelnerCondition_iff_hasFoelnerSequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:38:38.311512+00:00
-- url     : https://prove2.me/theorems/47482ac9-638a-4e9d-8957-09fee673b16a
-- title:
--   Lemma 3.4 — the Følner condition is equivalent to having a Følner sequence
-- statement:
--   For a **countable** group $G$, the Følner condition holds if and only if $G$ has
--   a Følner sequence.
--
--   Explicitly: "for every finite $A$ and $\varepsilon > 0$ there is a finite nonempty $F$ with
--   $|aF \,\triangle\, F|/|F| \le \varepsilon$ for all $a \in A$" is equivalent to "there is a
--   sequence of finite nonempty $F_n$ with $|gF_n \,\triangle\, F_n|/|F_n| \to 0$ for every
--   $g \in G$".
--
--   Countability is a typeclass hypothesis and is needed for the forward direction, where the
--   sequence is built by exhausting $G$ by an ascending chain of finite subsets. The source states
--   the definition of a Følner sequence for discrete countable groups, noting that for uncountable
--   discrete groups one uses nets instead; nets are not formalised here.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 9, Lemma 3.4; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Foelner

namespace Garrido

theorem satisfiesFoelnerCondition_iff_hasFoelnerSequence (G : Type*) [Group G] [Countable G] :
    SatisfiesFoelnerCondition G ↔ HasFoelnerSequence G := by
  sorry

end Garrido
