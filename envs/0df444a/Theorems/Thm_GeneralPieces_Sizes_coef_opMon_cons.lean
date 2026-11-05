-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_coef_opMon_cons
-- name    : GeneralPieces.Sizes.coef_opMon_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:39.796201+00:00
-- url     : https://prove2.me/theorems/0651d4f5-4414-4c96-a600-04aa0a64515d
-- title:
--   Sizes: coef op Mon cons
-- statement:
--   By (O2), since ∇_k t^σ = k·m_k(σ)·t^σ/t_k and the coefficient of t^{σ'} in t_l·f is that of
--   t^{σ'}/t_l in f: an entry of the table of t_n·a' as a combination of entries of the table of a'.
--   The sums run over the different parts l of σ' and k of σ. Proved from the recursion that defines the
--   matrices `ClauseBound.Boson.op`, which is (O2), through `GeneralPieces.stBridge`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L64-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L64-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.coef_opMon_cons (n : ℕ+) (a' : List ℕ+) (r : ℤ) (σ' σ : Ptn) :
    coef σ' (opMon (n :: a') r (tpow σ)) =
      ∑ l ∈ σ'.toFinset, ((binom (((l : ℕ) : ℤ) - 1) ((n : ℤ) - 1) : ℤ) : ℚ) * coef (σ'.erase l) (opMon a' (r - (l : ℕ)) (tpow σ)) +
        ∑ k ∈ σ.toFinset, ((binom (-((k : ℕ) : ℤ) - 1) ((n : ℤ) - 1) * ((k : ℕ) * σ.count k) : ℤ) : ℚ) *
          coef σ' (opMon a' (r + (k : ℕ)) (tpow (σ.erase k))) := by sorry
