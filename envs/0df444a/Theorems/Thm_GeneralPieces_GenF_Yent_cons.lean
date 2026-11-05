-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Yent_cons
-- name    : GeneralPieces.GenF.Yent_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:13.279516+00:00
-- url     : https://prove2.me/theorems/33c94fe2-d7e9-4b3a-852b-cdbac3570d03
-- title:
--   Gen F: Yent cons
-- statement:
--   Y(t_n·t^ν, ω) = J_n^+(ω)·Y(t^ν, ω) + Y(t^ν, ω)·J_n^-(ω), entry by entry: the recursion for the
--   operators t^ν[r], multiplied by the powers of ω.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L60-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L60-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem GeneralPieces.GenF.Yent_cons (e : ℤ → R) (he : ∀ x y, e x * e y = e (x + y)) (n : ℕ) (b : List ℕ) (τ σ : Multiset ℕ) :
    Yent e (n :: b) τ σ = ∑ l ∈ τ.toFinset, ((bet n l : ℚ) • e ((l : ℤ) - n)) * Yent e b (τ.erase l) σ +
      ∑ k ∈ σ.toFinset, (((k : ℚ) * σ.count k * bet n (-(k : ℤ))) • e (-(k : ℤ) - n)) * Yent e b τ (σ.erase k) := by sorry
