-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_5_5
-- name    : MinBisectFPT.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:13.716073+00:00
-- url     : https://prove2.me/theorems/6239f57c-a9cc-4e1c-8955-2386e1f2efd4
-- title:
--   Lemma 5.5 — the recursive calls of Line 8 are legal
-- statement:
--   Consider a call $\mathrm{Decompose}(D)$ of Algorithm 2 past Line 3, on a connected graph $G$ with $k\ge1$, with $H=H_D$, $|Z|=2k+1$ and $Z\subseteq\beta\subseteq V(H)$.
--   Suppose every component of $H-\beta$ has at most $2k$ neighbours in $H$. Then every component $D'$ of $H-\beta$ satisfies $D'\subseteq D\setminus\beta$, $G[D']$ is connected, $N_G(D')=N_H(D')\subseteq\beta$, and $|N_G(D')|\le2k$. In particular $D'$ is a legal input of $\mathrm{Decompose}$.
--
--   Differences from the source:
--   - generalization: the current bag $\beta$ in a call of Algorithm 2 → any $\beta$ with the listed invariants; reason: the loop maintains them, so every state of the loop is an instance
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.5, p.19

import Mathlib
import Definitions.Def_MinBisectFPT_IsDecomposeRun

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 5.5.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 5.5, p.19: "In Line 8, every component D′ of H − β satisfies D′ ⊆ D \ β,
G[D′] is connected, N_G(D′) = N_H(D′) ⊆ β, and |N_G(D′)| ≤ 2k. In particular, the recursive calls
are legal." -/
theorem lemma_5_5 {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) (hk : 1 ≤ k)
    (D Z β : Finset (Fin n)) (hsetup : IsCallSetup G k D Z) (hβ : β ⊆ callVerts G D) (hI1 : Z ⊆ β)
    (hI2 : InvI2 (callGraph G D) (callVerts G D) β k) (D' : Finset (Fin n))
    (hD' : IsComponent (callGraph G D) (callVerts G D \ β) D') :
    D' ⊆ D \ β ∧ (G.induce (D' : Set (Fin n))).Connected ∧
      nbr G D' = nbr (callGraph G D) D' ∧ nbr (callGraph G D) D' ⊆ β ∧ (nbr G D').card ≤ 2 * k ∧
        IsLegalCall G k D' := by sorry

end MinBisectFPT
