-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_slotHit_card
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:30:32.000995+00:00
-- url     : https://prove2.me/theorems/8eb19699-0617-48f8-b884-535c65cbfbdb
-- title:
--   Each slot hits exactly $K(R-1)$ residues modulo $q$
-- statement:
--   **Setting.** Let $r\ge1$ and $d:\{0,\dots,r-1\}\to\mathbb N$, with odd slot lengths $L_i=2d_i+1$, period length $P=\sum_{i<r}L_i$ and prefixes $\pi_i=\sum_{j<i}L_j$. Fix natural numbers $R$ (periods per chunk), $K$ (number of chunks) and $q\ge1$. The center of slot $i$ in period $p$ of chunk $k$ after a shift $s$ is $c(s,k,p,i)=kRP+pP+s+\pi_i+d_i+1$. For a sign $e\in\{+,-\}$ and $x\in\mathbb N$ let $\sigma_q(e,x)\in\mathbb Z/q\mathbb Z$ be the residue of $x$ if $e=+$ and of $-x$ if $e=-$.
--
--   - *Slot choices.* A slot choice $\omega$ assigns to every chunk $k\in\{0,\dots,K-1\}$ a shift and a sign, $\omega(k)=(s_k,e_k)\in\{0,\dots,P-1\}\times\{+,-\}$.
--   - *Hits.* A residue $u\in\mathbb Z/q\mathbb Z$ is hit by slot $i$ under $\omega$ if $u=\sigma_q\big(e_k,c(s_k,k,p,i)\big)$ for some chunk $k\in\{0,\dots,K-1\}$ and some period $p\in\{0,\dots,R-2\}$.
--
--   **Theorem.** Let $q\ge1$ and $2KRP<q$, let $i$ be a slot and let $\omega$ be any slot choice. Then
--
--   $$
--   \big|\{u\in\mathbb Z/q\mathbb Z:\ u\text{ is hit by slot } i\text{ under }\omega\}\big|=K(R-1) .
--   $$
--
--   Equivalently, the $K(R-1)$ signed centers $\sigma_q\big(e_k,c(s_k,k,p,i)\big)$, for $0\le k<K$ and $0\le p\le R-2$, are pairwise distinct modulo $q$, whatever the shifts and signs chosen by $\omega$. Thus the number of residues hit by each slot does not depend on the random choice, which fixes the number of vertices of the slot hypergraph.
--
--   **Formalization Note** The hit predicate is `slotHit d R K q i ω` (made decidable classically), slot choices are `SlotChoices d K = Fin K → Fin P × Bool`, and `[NeZero q]` encodes $q\ge1$. The period index ranges over `Fin (R-1)`, with truncated subtraction, so for $R=0$ both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L464-L480

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
attribute [local instance] Classical.propDecidable

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.slotHit_card (d : Fin r → ℕ) (R K q : ℕ) [NeZero q] (i : Fin r)
    (hq : 2*(K*(R*periodLength (oddLengths d)))<q) (ω : SlotChoices d K) :
    (Finset.univ.filter (fun t : ZMod q ↦ slotHit d R K q i ω t)).card=K*(R-1) := by sorry
