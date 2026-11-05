-- Prove2me | Theorems.Thm_GeneralPieces_GenF_map_eq_fP
-- name    : GeneralPieces.GenF.map_eq_fP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:13:10.5951+00:00
-- url     : https://prove2.me/theorems/85424cab-2576-4295-8d84-dfef37416976
-- title:
--   Gen F: map eq f P
-- statement:
--   ⟨Y(a, u)·Y(b, v)⟩ = Σ_r ⟨a[r]∘b[−r]⟩·u^{r−h'}·v^{−r−h}: if g has the coefficients ⟨τ|Y(b, v)|σ'⟩
--   and the form ℓ has the values ⟨σ|Y(a, u)|τ⟩, then ℓ applied to g is f₊.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L69-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/YY.lean#L69-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_YY
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.map_eq_fP (h0 : StOp0) {a b : List ℕ} {σ σ' : Multiset ℕ} (hσ' : 0 ∉ σ') (hw : σ.sum = σ'.sum) (ℓ : Vu →ₗ[Lu] Lu)
    (hℓ : ∀ τ : Multiset ℕ, ℓ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) = C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum))
    (g : Tv) (hg : ∀ τ : Multiset ℕ, bra τ g = ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum)) :
    g.map ℓ = fP a b σ σ' := by sorry
