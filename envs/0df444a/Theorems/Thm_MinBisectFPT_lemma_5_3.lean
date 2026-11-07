-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_3
-- name    : MinBisectFPT.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:16.544394+00:00
-- url     : https://prove2.me/theorems/9e2b928c-6778-4df4-825a-e5fdb38ec21e
-- title:
--   Lemma 5.3 — a breaking set yields a considered set of positive excess
-- statement:
--   Consider a call $\mathrm{Decompose}(D)$ of Algorithm 2 past Line 3, on a connected graph $G$ with $k\ge1$, with $H=H_D$, $|Z|=2k+1$ and $Z\subseteq\beta\subseteq V(H)$.
--   Let $X\subseteq V(H)$ satisfy $|\delta(X)|\le k$, $|X\cap Z|\le k$ and $|X\cap\beta|\ge3k+1$. Then some set $R$ under consideration satisfies $\mathrm{ex}(R)\ge1$.
--
--   The search for such a set among reachable sets of important cuts is what keeps the construction single-exponential.
--
--   Differences from the source:
--   - generalization: the current bag $\beta$ in a call of Algorithm 2 → any $\beta$ with the listed invariants; reason: the loop maintains them, so every state of the loop is an instance
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.3, p.18

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.3.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.3, p.18: "Let X ⊆ V(H) satisfy |δ(X)| ≤ k, |X ∩ Z| ≤ k and
|X ∩ β| ≥ 3k + 1. Then some reachable set R under consideration satisfies ex(R) ≥ 1." -/
theorem lemma_5_3 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k)
    (D Z β : Finset (Fin n)) (hsetup : IsCallSetup G k D Z) (hβ : β ⊆ callVerts G D) (hI1 : Z ⊆ β)
    (X : Finset (Fin n)) (hX : X ⊆ callVerts G D) (hcut : cutSize (callGraph G D) X ≤ k)
    (hXZ : (X ∩ Z).card ≤ k) (hXβ : 3 * k + 1 ≤ (X ∩ β).card) :
    ∃ R, IsConsidered (callGraph G D) Z β k R ∧ 1 ≤ excess (callGraph G D) Z β R := by sorry

end MinBisectFPT
