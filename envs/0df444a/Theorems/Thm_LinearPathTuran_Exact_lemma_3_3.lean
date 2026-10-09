-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_3_3
-- name    : LinearPathTuran.Exact.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:15.198408+00:00
-- url     : https://prove2.me/theorems/2c411fb4-4d72-4e9d-ace4-8d6fc2fea017
-- title:
--   Lemma 3.3 — if no member of J contains D, then F[D] lies in exactly one member of F*
-- statement:
--   Let $k,s$ be positive integers and let $\mathcal F^*$ be a $(k,s)$-homogeneous family on $[n]$ with $k$-partition $(X_1,\dots,X_k)$ and intersection pattern $\mathcal J$. Let $D\subseteq[k]$ be such that no member of $\mathcal J$ contains $D$. For $F\in\mathcal F^*$ write $F[D]=F\cap\bigcup_{i\in D}X_i$. Then
--   $$\deg_{\mathcal F^*}(F[D])=\big|\{F'\in\mathcal F^*: F[D]\subseteq F'\}\big|=1 .$$
--
--   In words, the projection of $F$ onto the parts indexed by $D$ is contained in no other member of $\mathcal F^*$. It is the step behind the rank bound (Proposition 3.4).
--
--   **Formalization Note** $F[D]$ is the set of vertices of $F$ whose part index lies in $D$.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 5, Lemma 3.3

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Lemma 3.3, p. 5: if no member of the intersection pattern contains `D`, then the projection
`F[D] = F ∩ ⋃_{i ∈ D} X_i` of a member `F` lies in no other member. -/
theorem lemma_3_3 (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (χ : Fin n → Fin k) (J : Finset (Finset (Fin k))) (hH : IsHomogeneous s 𝓕 χ J)
    (D : Finset (Fin k)) (hD : ∀ B ∈ J, ¬ D ⊆ B) (F : Finset (Fin n)) (hF : F ∈ 𝓕) :
    #(𝓕.filter (fun F' => F.filter (fun v => χ v ∈ D) ⊆ F')) = 1 := by sorry

end LinearPathTuran.Exact
