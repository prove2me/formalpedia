-- Prove2me | Theorems.Thm_GeneralPieces_Series_sum_list_comm
-- name    : GeneralPieces.Series.sum_list_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:37.025024+00:00
-- url     : https://prove2.me/theorems/e506580d-58d9-4dd9-a49f-7943b818965a
-- title:
--   Series: sum list comm
-- statement:
--   A sum over a finite set of sums over a list is the sum over the list of the sums over the set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L39-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem GeneralPieces.Series.sum_list_comm {ι α : Type} (s : Finset ι) (A : List α) (f : ι → α → ℤ) : ∑ i ∈ s, (A.map (f i)).sum = (A.map fun c => ∑ i ∈ s, f i c).sum := by sorry
