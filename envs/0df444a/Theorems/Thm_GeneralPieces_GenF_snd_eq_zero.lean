-- Prove2me | Theorems.Thm_GeneralPieces_GenF_snd_eq_zero
-- name    : GeneralPieces.GenF.snd_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:15:57.901205+00:00
-- url     : https://prove2.me/theorems/1c97e8a3-7443-455a-b211-a3334c24a03f
-- title:
--   Gen F: snd eq zero
-- statement:
--   In a splitting of x^μ·x'^ν the first factor has the full weight only if the second is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L89-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Assemble.lean#L89-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Kappa
import Definitions.Def_ClauseBound_Boson_Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_GeneralPieces_GenF_Assemble
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries Finset

theorem GeneralPieces.GenF.snd_eq_zero {a b : List ℕ} (ha : Pos a) (hb : Pos b) {p : (X →₀ ℕ) × (X →₀ ℕ)} (hp : p ∈ antidiagonal (ex a b)) (hw : wtX p.1 = a.sum + b.sum) :
    p.2 = 0 := by sorry
