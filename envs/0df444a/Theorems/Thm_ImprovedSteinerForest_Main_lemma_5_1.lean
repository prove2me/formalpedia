-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_5_1
-- name    : ImprovedSteinerForest.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:27:22.789974+00:00
-- url     : https://prove2.me/theorems/0976265c-189c-4e3c-bf4d-1007a4e1f861
-- title:
--   Lemma 5.1 — safe deletion spaces: deleting the forest edges whose rows lie in the chosen spaces keeps (F ∖ D) ∪ L feasible
-- statement:
--   Let $F$ be a feasible forest, with rows $w_f\in\mathbb F_2^P$ ($w_f(p)=1$ iff $f$ lies on the path of $p$ in $F$). Consider purchases $i=1,\dots,m$ with pairwise disjoint label sets $K_i\subseteq P$, bought bases $B_i\subseteq K_i$, and an edge set $L$ that connects every bought pair. For each purchase choose a subspace $W_i\subseteq\mathbb F_2^{K_i}$ on which restriction to $B_i$ is injective. Delete every edge of $F$ whose full row belongs to one of these spaces, and let $D$ be the deleted edge set:
--   $$D=\{f\in F:\ w_f\in W_1\cup\dots\cup W_m\}.$$
--   Then $(F\setminus D)\cup L$ is feasible.
--
--   This is the safety condition behind the bound on the optimum after a purchase (Theorem 5.2): it lets the analysis delete optimum edges whose demands are rerouted through the bought connections.
--
--   **Formalization Note.** $\mathbb F_2^{K}$ is the subspace of $\mathbb F_2^P$ of vectors vanishing outside $K$ ("extend vectors on $K$ to vectors on $P$ by zero", p. 26). Injectivity of restriction to $B_i$ is stated as: the only vector of $W_i$ vanishing on $B_i$ is $0$.
--
--   Differences from the source:
--   - generalization: "an optimum forest F of cost opt" with every unused edge removed → any feasible forest `F`; reason: the proof uses only the identity (5.1), which holds for every feasible forest (an edge with zero row lies in every space and is deleted); a pruned optimum forest is a feasible forest.
--   - generalization: the purchases of a compatible collection (label set `K`, cut space, bought basis `B`) → arbitrary pairwise disjoint label sets `K i` with `B i ⊆ K i`; reason: compatibility means disjoint label sets and `B ⊆ K`, and nothing else about the candidates is used.
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs; reason: contraction produces multigraphs (p. 13); a simple network is a special case.
--   - encoding: `F₂^K` → vectors of `I.Pair → ZMod 2` supported on `K` (`supportedOn K`); reason: the paper's extension by zero.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 27, Lemma 5.1

import Mathlib
import Definitions.Def_ImprovedSteinerForest_Main_Instance

namespace ImprovedSteinerForest.Main

open scoped Classical in
/-- Lemma 5.1 (Safe deletion spaces, p. 27): `F` a feasible forest with rows `w_f`; a compatible
collection of purchases, purchase `i` with label set `K i` (pairwise disjoint), bought basis
`B i ⊆ K i`, and `L` connecting every bought pair. For each purchase choose a subspace
`W i ⊆ F₂^{K i}` on which restriction to `B i` is injective, and delete every edge of `F` whose full
row lies in one of these spaces. If `D` is the deleted set, `(F \ D) ∪ L` is feasible. -/
theorem lemma_5_1 (I : Instance) (F : Finset I.Edge) (hF : I.IsForest F) (hFfeas : I.Feasible F)
    (m : ℕ) (K B : Fin m → Finset I.Pair)
    (hK : ∀ i i', i ≠ i' → Disjoint (K i) (K i')) (hB : ∀ i, B i ⊆ K i)
    (L : Finset I.Edge) (hL : ∀ i, ∀ p ∈ B i, I.Connected L (I.s p) (I.t p))
    (W : Fin m → Submodule (ZMod 2) (I.Pair → ZMod 2))
    (hW : ∀ i, W i ≤ I.supportedOn (K i))
    (hinj : ∀ i, ∀ x ∈ W i, (∀ p ∈ B i, x p = 0) → x = 0) :
    I.Feasible ((F \ F.filter (fun f => ∃ i, I.row F f ∈ W i)) ∪ L) := by sorry

end ImprovedSteinerForest.Main
