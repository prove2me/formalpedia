-- Prove2me | Theorems.Thm_GoodmanWitten_strong_cross_section_estimate
-- name    : GoodmanWitten.strong_cross_section_estimate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:57:46.686593+00:00
-- url     : https://prove2.me/theorems/afa45652-ccc9-4570-bf93-194f43b30b63
-- title:
--   Hard-sphere cross section $\sigma\approx2.0A^{2/3}\times10^{-25}$ cm$^2$
-- statement:
--   Let a strongly interacting particle scatter from a nucleus of mass number $A>0$ through a square-well potential of radius $R = 1.25A^{1/3}\times10^{-13}$ cm, with low-energy cross section $\sigma = 4\pi R^2$. Then there is a constant $C$ with $|C/2.0 - 1|\le0.05$ such that for all $A>0$
--   $$
--   \sigma = C\,A^{2/3}\times10^{-25}\ \mathrm{cm}^2 .
--   $$
--
--   **Formalization Note** 5% relative tolerance on the printed coefficient.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3062, right column, section (iii), paragraph 2

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem strong_cross_section_estimate : ∃ C : ℝ, |C / 2.0 - 1| ≤ 0.05 ∧
    ∀ A : ℝ, 0 < A → strongCrossSection A = C * A ^ ((2 : ℝ) / 3) * 1e-25 := by sorry

end GoodmanWitten
