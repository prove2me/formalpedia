-- Prove2me | Theorems.Thm_MooreFoelner_card_Rf_sub_two_le_three_mul_wordLength
-- name    : MooreFoelner.card_Rf_sub_two_le_three_mul_wordLength
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:26:59.038992+00:00
-- url     : https://prove2.me/theorems/10ca3c16-901e-470b-819a-479ecce8f108
-- title:
--   Burillo–Cleary–Stein, as Moore applies it — word length is at least (k−2)/3
-- statement:
--   For every $f$ in Moore's $F$, if $k$ is the number of leaves of the trees of its reduced diagram, then the word length of $f$ with respect to $\Gamma = \{x_0^{\pm1}, x_1^{\pm1}\}$ is at least $(k - 2)/3$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 19, proof of Theorem 1.1 (citing Burillo–Cleary–Stein, Theorem 1 and Proposition 2)

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem card_Rf_sub_two_le_three_mul_wordLength (f : MooreF) :
    ((Rf (toMap f)).card : ℝ) - 2 ≤ 3 * wordLength gens f := by
  sorry

end MooreFoelner
