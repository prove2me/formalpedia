-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_2
-- name    : MinBisectFPT.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:26.766503+00:00
-- url     : https://prove2.me/theorems/48e3b285-b5bd-49fd-90c7-029b8accba5c
-- title:
--   Lemma 5.2 — a loop step shrinks $\beta$ and keeps (I1), (I2)
-- statement:
--   Consider a call $\mathrm{Decompose}(D)$ of Algorithm 2 past Line 3, on a connected graph $G$ with $k\ge1$, with $H=H_D$, $|Z|=2k+1$ and $Z\subseteq\beta\subseteq V(H)$.
--   Suppose that every component $C$ of $H-\beta$ satisfies $|N_H(C)|\le2k$, which with $Z\subseteq\beta$ are the invariants (I2) and (I1). Then every iteration of Lines 5–7, leading from $\beta$ to $\beta'$, gives $|\beta'|<|\beta|$, $\beta'\subseteq V(H)$, $Z\subseteq\beta'$, and every component $C'$ of $H-\beta'$ satisfies $|N_H(C')|\le2k$.
--
--   Differences from the source:
--   - generalization: the current bag $\beta$ in a call of Algorithm 2 → any $\beta$ with the listed invariants; reason: the loop maintains them, so every state of the loop is an instance
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
--   - generalization: "strictly decrease $|\beta|$ and preserve (I1) and (I2)" → also the clause `β ⊆ V(H)`; reason: implicit on the page and used by the later lemmas
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.2, p.18

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.2.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.2, p.18: "Lines 5–7 strictly decrease |β| and preserve (I1) and
(I2)." The clause `β′ ⊆ V(H)` is implicit on the page. -/
theorem lemma_5_2 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k)
    (D Z β : Finset (Fin n)) (hsetup : IsCallSetup G k D Z) (hβ : β ⊆ callVerts G D) (hI1 : Z ⊆ β)
    (hI2 : InvI2 (callGraph G D) (callVerts G D) β k) (β' : Finset (Fin n))
    (hstep : LoopStep (callGraph G D) (callVerts G D) Z k β β') :
    β'.card < β.card ∧ β' ⊆ callVerts G D ∧ Z ⊆ β' ∧
      InvI2 (callGraph G D) (callVerts G D) β' k := by sorry

end MinBisectFPT
