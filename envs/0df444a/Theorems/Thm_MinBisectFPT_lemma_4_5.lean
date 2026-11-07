-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_4_5
-- name    : MinBisectFPT.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:38.119285+00:00
-- url     : https://prove2.me/theorems/0c5c88e7-3618-412d-b814-bbc5867314f6
-- title:
--   Lemma 4.5 — listing the candidates through a vertex
-- statement:
--   Let $H$ be a graph on $n$ vertices with $m$ edges, $\beta\subseteq V(H)$, $v\in\beta$, $k\ge0$ and $q\ge1$. One can list, in time $O(8^{k+q}(k+q)(n+m))$, a family $\mathcal{U}_v$ of at most $8^{k+q}$ subsets of $\beta$ that contains every candidate containing $v$.
--
--   Precisely, there is a program and a constant $C$ such that, for every instance and every word size $W$ with $(n+m+k+q+2)^C\le2^W$, the program writes such a family within $C\,8^{k+q}(k+q)(n+m)$ steps.
--
--   With $H=G_t$ on the vertices of $G$, $V(H)=\gamma(t)$ and $q=3k$ this is the printed lemma, since $G_t$ has at most as many edges as $G$.
--
--   Differences from the source:
--   - generalization: $H=G_t$, $q=3k$, $\beta=\beta(t)$ in a decomposition with (D1)–(D3), with $n,m$ those of $G$ → any graph $H$ on `Fin n`, any $\beta$, $k$, $q\ge1$, with `edgeCount H` for $m$; reason: the statement specializes as above, and `edgeCount` of $G_t$ is at most $m$
--   - reading: an unspecified machine with a time linear in the graph size → the published unit-cost word RAM on preloaded memory, program and constant before the instance, with the word bound `(n + edgeCount H + k + q + 2)^C ≤ 2^W`; reason: the printed time cannot hold on a Turing machine, which needs more than linear time to read a graph; this is the standard word size
--   - encoding: graphs $G_t$, $H_D$ on their own vertex sets → the same graphs on the ambient `Fin n`, with the other vertices isolated and every $X\subseteq V(H)$ written `X ⊆ VH`; reason: isolated ambient vertices change no cut and no neighbourhood
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.5, p.14

import Mathlib
import Definitions.Def_FixedMachinePrec_RAM
import Definitions.Def_MinBisectFPT_encodeCuts
import Definitions.Def_MinBisectFPT_IsCandidate

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 4.5.** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.5, p.14: "Let v ∈ β. One can list, in time O(8^{k+q}(k + q)(n + m)), a family
U_v of at most 8^{k+q} subsets of β that contains every candidate containing v."

**Formalization Note** Any graph `H` on `Fin n`, any `β`, `k` and `q ≥ 1`, on the published unit-cost word
RAM with preloaded memory (a time linear in `n + m` needs one), `P` and `C` before the instance. `H := G_t`,
`VH := γ(t)`, `q := 3k` gives the printed lemma; there `n` is that of `G` and `edgeCount G_t ≤ m`. -/
theorem lemma_4_5 :
    ∃ (P : List FixedMachinePrec.RAMInstr) (C : ℕ),
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (β : Finset (Fin n)) (v : Fin n) (k q W : ℕ),
        v ∈ β → 1 ≤ q → (n + edgeCount H + k + q + 2) ^ C ≤ 2 ^ W →
        ∃ L : List (Finset (Fin n)), L.length ≤ 8 ^ (k + q) ∧ (∀ S ∈ L, S ⊆ β) ∧
          (∀ VH U, IsCandidate H VH β q k U → v ∈ U → U ∈ L) ∧
          ∃ b, FixedMachinePrec.ramExec (W := W) P (C * 8 ^ (k + q) * (k + q) * (n + edgeCount H)) 0
            (familyMem W H β v k q) [] [] = some (b, encodeFamily L) := by sorry

end MinBisectFPT
