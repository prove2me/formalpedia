-- Prove2me | Theorems.Thm_GeneralPieces_Series_terms_vac
-- name    : GeneralPieces.Series.terms_vac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:09.531462+00:00
-- url     : https://prove2.me/theorems/49af3ab2-e323-45eb-8a7c-e3029c84acfc
-- title:
--   Series: terms vac
-- statement:
--   For a list of terms c = (q, N, n) with N ≤ H, n = 0 when N < H and n = 1 when N = H, the sum of
--   q·e^N·φ(n) is (the sum of the q of the terms with N = H)·e^H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L104-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Constant.lean#L104-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_ReadOff
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_GeneralPieces_Series_Constant
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset

theorem GeneralPieces.Series.terms_vac (φ : L →ₐ[ℚ] S) (e : S) (H : ℕ) (l : List (ℚ × ℕ × L)) (hl : ∀ c ∈ l, c.2.1 ≤ H) (ht : ∀ c ∈ l, c.2.1 = H → c.2.2 = 1)
    (hv : ∀ c ∈ l, c.2.1 < H → c.2.2 = 0) :
    (l.map fun c => c.1 • (e ^ c.2.1 * φ c.2.2)).sum = ((l.filter fun c => c.2.1 = H).map fun c => c.1).sum • e ^ H := by sorry
