-- Prove2me | Theorems.Thm_Groundwork_BitCut_expand
-- name    : Groundwork.BitCut.expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:22.558944+00:00
-- url     : https://prove2.me/theorems/f022e304-ae18-4f1f-bb1b-da36046c5632
-- title:
--   Bit Cut: expand
-- statement:
--   Multiplying out: one lemma for both cuts (and for the Bell basis). a, b are the two ends on one
--   side, c', d those
--   on the other.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L93-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Cross/Cuts.lean#L93-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Cross_Cuts
set_option autoImplicit false
section
section
open Groundwork
open Finset

theorem Groundwork.BitCut.expand (c : BitCut) (D0 D1 : Bool → Bool → Bool → Bool → ℤ)
    (h0 : ∀ a b c' d, D0 a b c' d = ∑ h, c.top h a b * c.bot0 h c' d)
    (h1 : ∀ a b c' d, D1 a b c' d = ∑ h, c.top h a b * c.bot1 h c' d) {n : ℕ} (i : ℕ) (a b c' d : Bits n) :
    ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
        (∏ k ∈ S, D1 (a k) (b k) (c' k) (d k)) * ∏ k ∈ Sᶜ, D0 (a k) (b k) (c' k) (d k)
      = ∑ β : Fin n → Bell, c.Top β a b * c.Bot i β c' d := by sorry
