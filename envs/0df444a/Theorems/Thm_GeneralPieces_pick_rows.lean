-- Prove2me | Theorems.Thm_GeneralPieces_pick_rows
-- name    : GeneralPieces.pick_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:25.833861+00:00
-- url     : https://prove2.me/theorems/b17b96d1-78e0-4367-8056-adabdf4c4b81
-- title:
--   General Pieces: pick rows
-- statement:
--   On a (K_ℓ, λ)-clique the program picks level ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L51-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L51-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Descend
import Definitions.Def_GeneralPieces_Rec_Level
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Alg_Enum
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_ClauseBound_Alg_CertEnum
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_GeneralPieces_Rec_PartB
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

theorem GeneralPieces.pick_rows (P : PiecesF) (x₀ : ℕ) (hx : 18 ≤ x₀) (l lam B : ℕ) (I : PInst) (hI : WFe (K x₀ l) lam B I) :
    (Pick.pick P x₀ (List.replicate I.2.length ())).2 = idx P x₀ l := by sorry
