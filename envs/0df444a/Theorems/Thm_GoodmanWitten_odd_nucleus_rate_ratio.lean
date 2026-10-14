-- Prove2me | Theorems.Thm_GoodmanWitten_odd_nucleus_rate_ratio
-- name    : GoodmanWitten.odd_nucleus_rate_ratio
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:56:14.441475+00:00
-- url     : https://prove2.me/theorems/51d6be56-2995-4d7c-b60f-ed2959c8d20b
-- title:
--   Up- vs down-squark exchange: rate ratio roughly 100
-- statement:
--   With $g_A = 1.2$, the ratio of the squared single-nucleon matrix elements of Eq. (4) for the favoured and unfavoured quark flavour satisfies
--   $$
--   100 \le \left(\frac{1+g_A}{1-g_A}\right)^2 < 1000 .
--   $$
--   Since rates are proportional to squared matrix elements, the rate for up-squark exchange on odd-$Z$ nuclei (or down-squark exchange on odd-$N$ nuclei) is roughly 100 times the rate for the opposite flavour.
--
--   **Formalization Note** "Roughly 100 times" is read as order of magnitude $10^2$.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3061, left column, paragraph 'From Eq. (4) we expect...' and g_A = 1.2 below the isovector relation

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem odd_nucleus_rate_ratio :
    (100 : ℝ) ≤ ((1 + 1.2) / (1 - 1.2)) ^ 2 ∧ ((1 + 1.2) / (1 - 1.2)) ^ 2 < (1000 : ℝ) := by sorry

end GoodmanWitten
