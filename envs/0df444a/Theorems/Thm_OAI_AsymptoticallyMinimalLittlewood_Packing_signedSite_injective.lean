-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signedSite_injective
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:27:03.795368+00:00
-- url     : https://prove2.me/theorems/15599a99-0258-408a-ae7c-4c2f84b40e69
-- title:
--   Signed residues $\pm x \bmod q$ with $1\le x\le A$ and $2A<q$ are pairwise distinct
-- statement:
--   For a natural number $q$, a sign $e\in\{+,-\}$ and $x\in\mathbb N$ let $\sigma_q(e,x)\in\mathbb Z/q\mathbb Z$ denote the residue of $x$ if $e=+$ and of $-x$ if $e=-$.
--
--   Let $q,A,x,y$ be natural numbers with $2A<q$, $1\le x\le A$ and $1\le y\le A$. Then for all signs $e,f$
--
--   $$
--   \sigma_q(e,x)=\sigma_q(f,y)\iff e=f\ \text{ and }\ x=y .
--   $$
--
--   Thus the $2A$ residues $\pm1,\pm2,\dots,\pm A$ modulo $q$ are pairwise distinct, so a signed residue determines both its sign and its magnitude. In the slot construction, positions of slot centers are encoded as signed residues modulo a large prime, and this injectivity lets one recover the position and the sign from the residue.
--
--   **Formalization Note** The signed residue is `signedSite q e x`, with the sign encoded as a Boolean (`true` for $+$, `false` for $-$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L110-L123

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uJ
open scoped BigOperators
open Finset
variable {r : ℕ}

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.signedSite_injective {q A x y : ℕ} (hq : 2*A<q)
    (hx : 0<x) (hxA : x≤A) (hy : 0<y) (hyA : y≤A) (e f : Bool) :
    signedSite q e x=signedSite q f y ↔ e=f ∧ x=y := by sorry
