-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat27_exponent_injective_public
-- name    : LevyFoundations.leanlevy_chat27_exponent_injective_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:37:25.87691+00:00
-- url     : https://prove2.me/theorems/2a17c41b-fe1a-44fb-8b47-5b133dab1617
-- title:
--   Public wrapper Lévy-Khintchine exponent injectivity
-- statement:
--   Transfer of public source-exact triple injectivity to the wrapper Levy-Khintchine triple using definitional equality of Lévy-measure conditions and exponents.
-- source:
--   Direct definitional transport of accepted source-exact public triple extensionality b8123142; original slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; staged transport candidates/work_on/leanlevy_chat27_exponent_injective_transport_public_20261109.lean. Necessary intermediate following target 46afeb62 WA diagnostic.

import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_triple_ext_public

open MeasureTheory ProbabilityTheory

theorem LevyFoundations.leanlevy_chat27_exponent_injective_public
    (T U : LevyFoundations.LevyKhintchineTriple)
    (h : ∀ ξ : ℝ, LevyFoundations.exponent T ξ = LevyFoundations.exponent U ξ) :
    T = U := by sorry
