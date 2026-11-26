-- Prove2me | Theorems.Thm_O3_pairing_sub_left
-- name    : O3.pairing_sub_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:57.068982+00:00
-- url     : https://prove2.me/theorems/18763acb-a973-5b5f-97cf-179af629a675
-- title:
--   O3: pairing sub left
-- statement:
--   The O3 construction uses the pairing sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L31-L38
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L31-L38

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_sub_left {d : ℕ} (x y z : Vec d) :
    pairing (x - y) z = pairing x z - pairing y z := by sorry
