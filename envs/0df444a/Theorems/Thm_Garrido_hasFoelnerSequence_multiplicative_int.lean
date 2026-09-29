-- Prove2me | Theorems.Thm_Garrido_hasFoelnerSequence_multiplicative_int
-- name    : Garrido.hasFoelnerSequence_multiplicative_int
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:39:07.984987+00:00
-- url     : https://prove2.me/theorems/ee5634ad-016d-4565-91fc-0d34f5ce9d93
-- title:
--   Example 3.5 — the integers have a Følner sequence
-- statement:
--   The group of integers has a Følner sequence: there is a sequence of finite
--   nonempty subsets $F_n$ of $\mathbb{Z}$ with
--
--   $$\frac{|gF_n \,\triangle\, F_n|}{|F_n|} \longrightarrow 0 \quad (n \to \infty)$$
--
--   for every group element $g$.
--
--   This is the source's own assertion — "The group $\mathbb{Z}$ has a Følner sequence, namely
--   $F_n = \{-n, \dots, n\}$" — so what is claimed is the **existence** of such a sequence, with
--   the intervals $\{-n, \dots, n\}$ being the intended witness rather than part of the claim.
--
--   $\mathbb{Z}$ appears here as $\operatorname{Multiplicative} \mathbb{Z}$, the same group
--   written multiplicatively, because the mission's Følner definitions are stated for multiplicative
--   groups; addition of integers becomes the group operation and nothing about the content
--   changes.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 9, Example 3.5; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Foelner

namespace Garrido

theorem hasFoelnerSequence_multiplicative_int :
    HasFoelnerSequence (Multiplicative ℤ) := by
  sorry

end Garrido
