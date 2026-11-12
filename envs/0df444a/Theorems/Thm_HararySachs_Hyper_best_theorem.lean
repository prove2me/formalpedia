-- Prove2me | Theorems.Thm_HararySachs_Hyper_best_theorem
-- name    : HararySachs.Hyper.best_theorem
-- status  : Proved
-- author  : @milia
-- created : 2026-11-12T03:25:05.449728+00:00
-- url     : https://prove2.me/theorems/20463045-2396-4897-a9e9-1ac729168a40
-- title:
--   BEST theorem — Euler tours $=L\,\tau(D)\prod_v(\deg^-(v)-1)!$
-- statement:
--   This is the BEST theorem (de Bruijn–van Aardenne-Ehrenfest–Smith–Tutte, Theorem 5 of the paper), counted as Euler tours with a distinguished first arc.
--
--   Let $D$ be a directed multigraph on $[n]$ with arc multiplicities $m(u,v)$ (loops allowed) and $L>0$ arcs in total, where parallel arcs are distinguishable. Suppose $D$ is Eulerian: its set $V(D)$ of vertices of positive degree is nonempty, $\deg^+(v)=\deg^-(v)$ for every $v$, and $V(D)$ is weakly connected. Let $\tau(D)$ be the number of spanning arborescences of $V(D)$ oriented toward the least vertex of $V(D)$, with parallel arcs distinguished. Then the number of Euler tours of $D$, i.e. closed trails using every arc exactly once with a distinguished first position, is
--
--   $$
--   L\cdot\tau(D)\prod_{v\in V(D)}\bigl(\deg^-(v)-1\bigr)!.
--   $$
--
--   Equivalently, since each Euler circuit gives $L$ tours, $|\mathfrak E(D)|=\tau(D)\prod_{v\in V(D)}(\deg^-(v)-1)!$, which is the BEST theorem. Combined with Lemma 4, it yields Corollary 6, the closed form $\hat f\operatorname{tr}(A^{d(k-1)})=d(k-1)\,\tau(f)\prod_v(\deg^-(v)-1)!$ used in the proof of Lemma 13.
--
--   **Formalization Note** Tours are the mission's `numTours`: bijections $\sigma$ from positions `Fin L` onto the labeled arcs `Arcs m`, such that the head of each arc is the tail of the next, cyclically. The arborescence count is `numArb`, which encodes trees by parent maps weighted by the product of arc multiplicities. In-degree is used in the factorials, as in the mission's associated coefficient; in an Eulerian digraph it equals out-degree.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 6, Theorem 5 (BEST theorem) and Corollary 6, with the count |E(D)||𝔈(D)| of Euler tours from the proof of Lemma 4; original: van Aardenne-Ehrenfest and de Bruijn (1951), Smith and Tutte (1941)

import Mathlib
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

theorem best_theorem {n L : ℕ} (hL : 0 < L) (m : ArcMult n)
    (hm : (∑ u : Fin n, ∑ v : Fin n, m u v) = L) (hEu : IsEulerian m) :
    numTours m hL =
      L * numArb m * ∏ v ∈ active m, Nat.factorial (inDeg m v - 1) := by sorry

end HararySachs.Hyper
