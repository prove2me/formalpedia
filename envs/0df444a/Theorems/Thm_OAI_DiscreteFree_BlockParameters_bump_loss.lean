-- Prove2me | Theorems.Thm_OAI_DiscreteFree_BlockParameters_bump_loss
-- name    : OAI.DiscreteFree.BlockParameters.bump_loss
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:50:28.48929+00:00
-- url     : https://prove2.me/theorems/90285dfa-e174-44ab-a31d-01672a546cdf
-- title:
--   Parameter inequality $\frac{L}{K}(2pR+1)\le\frac{L}{4}$ for the block parameters
-- statement:
--   The metric blocks are built from natural-number parameters depending on $p\in\mathbb{N}$, among them
--   $$
--   L=10p,\qquad R=3L=30p,\qquad K=10p\,(R+1).
--   $$
--
--   **Theorem.** For every natural number $p\ge1$, with these values (as real numbers),
--   $$
--   \frac{L}{K}\,\bigl(2pR+1\bigr)\ \le\ \frac{L}{4}.
--   $$
--
--   In the block obstruction, an operator $T$ on the Lipschitz-free space with $\|T\|\le2p$ that moves the point evaluation $\delta_a$ at an anchor $a$ by less than $1$ is tested against a bump function of height $L$ and Lipschitz constant $L/K$ that equals $L$ at $a$. For a vertex $x$ at distance at most $R$ from $a$ one has $\|T\delta_x-\delta_a\|\le2pR+1$, so the pairing of $T\delta_x$ with the bump is at least $L-\frac{L}{K}(2pR+1)$; the inequality guarantees that this is at least $\frac{3L}{4}$.
--
--   **Formalization Note** The parameters are the natural numbers `BlockParameters.L p`, `R p`, `K p`, cast to $\mathbb{R}$; the division is real division, and $K>0$ for $p\ge1$, so no division-by-zero convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Parameters.lean#L59-L71

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters

open OAI OAI.DiscreteFree OAI.DiscreteFree.BlockParameters
open scoped BigOperators ENNReal

theorem OAI.DiscreteFree.BlockParameters.bump_loss {p : ℕ} (hp : 1 ≤ p) :
    (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (L p : ℝ)/4 := by sorry
