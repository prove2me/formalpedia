-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_lemma_4_3
-- name    : LiquidPoA.Kelly.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:03.753708+00:00
-- url     : https://prove2.me/theorems/f60e1123-732c-4bd4-871c-f2192278cc1d
-- title:
--   Lemma 4.3, p. 14 — class C makes each signal an equilibrium
-- statement:
--   For any $n$-player resource allocation mechanism $M$ in the class $\mathcal C$ and any $s\in\mathbb X_n$, the same signal vector is a pure Nash equilibrium of its affine game:
--
--   $$
--   s\in eq(G^M(s,1)).
--   $$
--
--   This is the equality condition used in Lemma 4.2. The class $\mathcal C$ asks for concavity of each player's own-signal allocation and convexity of her own-signal payment.
--
--   **Formalization Note** The valuations and budgets of $G^M(s,1)$ are constructed from $M$ and $s$; affordability is part of equilibrium.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 14, Lemma 4.3

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Lemma 4.3, p. 14: every vector in `𝕏ₙ` is an equilibrium of its affine game for a class-`𝒞` mechanism. -/
theorem lemma_4_3 {n : ℕ} (hn : 2 ≤ n) (M : Mechanism n)
    (hM : IsRAMechanism M) (hC : InClassC M)
    (s : Fin n → ℝ) (hs : InX s) :
    IsEquilibrium M (worstGame M s (⟨0, by omega⟩ : Fin n)) s := by sorry

end LiquidPoA.Kelly
