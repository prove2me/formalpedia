-- Prove2me | Theorems.Thm_NetInspect_Rate_corollary_EC_1
-- name    : NetInspect.Rate.corollary_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:04.507992+00:00
-- url     : https://prove2.me/theorems/29aed802-7e7f-48f0-9ca9-2d2ef3a18dc5
-- title:
--   Corollary EC.1, p. ec1 — F(S,T) ≤ Σ_{i∈S} F(i,T) and F(S,T) = Σ_{e∈T} F(S,e)
-- statement:
--   Let $\mathcal G=(\mathcal V,\mathcal E,\{\mathcal C_i\})$ be a detection model with detection function $F(S,T)=|\mathcal C_S\cap T|$. Then for all $S\subseteq\mathcal V$ and $T\subseteq\mathcal E$,
--   $$
--   F(S,T)\le\sum_{i\in S}F(\{i\},T)\qquad\text{(EC.6)},\qquad\qquad F(S,T)=\sum_{e\in T}F(S,\{e\})\qquad\text{(EC.7)}.
--   $$
--
--   The first inequality is the subadditivity of $F$ in the positioning, the second the additivity of $F$ in the attack plan. Both are used repeatedly in the bounds on the value of the inspection game.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. ec1, Corollary EC.1, (EC.6)–(EC.7)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Corollary EC.1 (p. ec1): (EC.6) `F(S, T) ≤ Σ_{i∈S} F(i, T)` and (EC.7) `F(S, T) = Σ_{e∈T} F(S, e)`. -/
theorem corollary_EC_1 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) :
    (∀ (S : Finset V) (T : Finset E), G.F S T ≤ ∑ i ∈ S, G.F {i} T) ∧
    (∀ (S : Finset V) (T : Finset E), G.F S T = ∑ e ∈ T, G.F S {e}) := by sorry

end NetInspect.Rate
