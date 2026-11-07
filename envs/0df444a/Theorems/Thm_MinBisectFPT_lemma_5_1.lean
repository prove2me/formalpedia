-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_1
-- name    : MinBisectFPT.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:17.95424+00:00
-- url     : https://prove2.me/theorems/b16e5358-cfa8-47ca-811f-9d906ac45203
-- title:
--   Lemma 5.1 — $|A\cap B|\le 2k$ in Line 6
-- statement:
--   Consider a call $\mathrm{Decompose}(D)$ of Algorithm 2 past Line 3, on a connected graph $G$ with $k\ge1$, with $H=H_D$, $|Z|=2k+1$ and $Z\subseteq\beta\subseteq V(H)$.
--   Let $R$ be under consideration with $\mathrm{ex}(R)\ge1$, let $Z_1$ be as in Line 5, and let $(A,B)$ be a separation of $H$ of minimum order with $Z_1\subseteq A$ and $Z\subseteq B$. Then
--   $$|A\cap B|\le|\delta(R)|+|R\cap Z|<|Z_1|,$$
--   and in particular $|A\cap B|\le 2k$.
--
--   Differences from the source:
--   - generalization: the current bag $\beta$ in a call of Algorithm 2 → any $\beta$ with the listed invariants; reason: the loop maintains them, so every state of the loop is an instance
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.1, p.18

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.1.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.1, p.18: "In Line 6, |A ∩ B| ≤ |δ(R)| + |R ∩ Z| < |Z1|. In particular,
|A ∩ B| ≤ 2k." The state is any state of the loop of Algorithm 2 at Line 6. -/
theorem lemma_5_1 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k)
    (D Z β : Finset (Fin n)) (hsetup : IsCallSetup G k D Z) (hβ : β ⊆ callVerts G D) (hI1 : Z ⊆ β)
    (R Z1 A B : Finset (Fin n)) (hR : IsConsidered (callGraph G D) Z β k R)
    (hex : 1 ≤ excess (callGraph G D) Z β R) (hZ1 : IsLine5 (callGraph G D) Z β R Z1)
    (hAB : IsMinSeparation (callGraph G D) (callVerts G D) Z1 Z A B) :
    (A ∩ B).card ≤ cutSize (callGraph G D) R + (R ∩ Z).card ∧
      cutSize (callGraph G D) R + (R ∩ Z).card < Z1.card ∧ (A ∩ B).card ≤ 2 * k := by sorry

end MinBisectFPT
