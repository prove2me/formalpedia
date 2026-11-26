-- Prove2me | Theorems.Thm_O3_pairing_finset_sum_left
-- name    : O3.pairing_finset_sum_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:57.172202+00:00
-- url     : https://prove2.me/theorems/7ff16479-1d40-4afc-91f9-778a3748e406
-- title:
--   O3: pairing finset sum left
-- statement:
--   The O3 construction uses the pairing finset sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L21-L29
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L21-L29

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_finset_sum_left {d : ℕ} {α : Type*}
    (s : Finset α) (f : α → Vec d) (x : Vec d) :
    pairing (∑ i ∈ s, f i) x = ∑ i ∈ s, pairing (f i) x := by sorry
