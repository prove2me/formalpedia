-- Prove2me | Theorems.Thm_ImplicitParityWL_lemma_3_2
-- name    : ImplicitParityWL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:14:07.743473+00:00
-- url     : https://prove2.me/theorems/cac9d8f5-c6c8-4f63-99f5-2e47e7dba2df
-- title:
--   Lemma 3.2 — the color-first variant has the same survival rounds
-- statement:
--   Let $G,H$ be colored graphs with $|\chi_G^{-1}(A)|=|\chi_H^{-1}(A)|$ for every color $A$, and let $m\ge1$ and $r\ge0$. From every game state, Duplicator survives $r$ rounds of $\mathrm{BP}_m(G,H)$ if and only if she survives $r$ rounds of its color-first variant.
--
--   This lets Duplicator's strategy answer one color class at a time.
--
--   Differences from the source: none.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Lemma 3.2, p.15

import Mathlib
import Definitions.Def_ImplicitParityWL_PebbleGame

namespace ImplicitParityWL

/-- **Lemma 3.2** (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, p.15): if corresponding color classes of `G` and `H` have equal sizes, then from every game
state Duplicator survives `r` rounds of `BP_m(G, H)` if and only if she survives `r` rounds of its color-first
variant. -/
theorem lemma_3_2 {K V W : Type*} [Fintype V] [Fintype W] (G : ColoredGraph K V)
    (H : ColoredGraph K W) (hclass : ∀ A : K, Nat.card {p : V // G.χ p = A} = Nat.card {q : W // H.χ q = A})
    (m : ℕ) (hm : 1 ≤ m) (r : ℕ) (S : GameState V W m) :
    Survives G H r S ↔ SurvivesCF G H r S := by sorry

end ImplicitParityWL
