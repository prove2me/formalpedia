-- Prove2me | Theorems.Thm_LowRankUnivariateSOS_UPair_ext
-- name    : LowRankUnivariateSOS.UPair.ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:41.339122+00:00
-- url     : https://prove2.me/theorems/a5c3ea63-1106-5c17-a48f-44fb696520fc
-- title:
--   UPair: ext
-- statement:
--   Extensionality for polynomial pairs. This is the basic way we identify two
--    candidate factorizations once their two coordinates agree.
--
--   Source: https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PolynomialModel.lean#L46-L51
-- source:
--   https://github.com/yuanchenyang/lean_low_rank_univariate_sos/blob/1fccd921a4530a088ab6e230f832041ab3c5c7f3/LowRankUnivariateSOS/PolynomialModel.lean#L46-L51

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
open scoped BigOperators
open LowRankUnivariateSOS.UPair

theorem LowRankUnivariateSOS.UPair.ext {u v : UPair} (hfst : u.fst = v.fst) (hsnd : u.snd = v.snd) : u = v := by sorry
