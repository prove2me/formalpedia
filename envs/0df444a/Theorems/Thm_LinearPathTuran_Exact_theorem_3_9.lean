-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_theorem_3_9
-- name    : LinearPathTuran.Exact.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:31.906028+00:00
-- url     : https://prove2.me/theorems/993c5f2d-9dec-4831-b027-af14b4cee413
-- title:
--   Theorem 3.9 — the canonical partition of a ℙ_ℓ-free family into type-1 homogeneous pieces and O(n^{k−2}) members
-- statement:
--   Let $k\ge 4$, $\ell\ge 1$ and $s\ge k\ell$. There is a constant $c=c(k,s)>0$ such that the following holds for every $n$. If $\mathcal F\subseteq\binom{[n]}{k}$ contains no $\mathbb P_\ell^{(k)}$, then $\mathcal F$ can be partitioned into subfamilies $\mathcal G_1,\dots,\mathcal G_m,\mathcal F_0$ such that each $\mathcal G_i$ is $(k,s)$-homogeneous with an intersection pattern $\mathcal J_i$ of rank $k-1$ and type 1, and
--   $$|\mathcal F_0|\le\frac{1}{c(k,s)}\binom{n}{k-2}.$$
--
--   The partition is called a *canonical partition* of $\mathcal F$; §§4–5 work with it throughout.
--
--   **Formalization Note** The paper's $c(k,s)$ is the constant of Lemma 3.1; here it is an existential constant chosen after $k,\ell,s$ and before $n$ and $\mathcal F$. The partition is written as $\mathcal F=\mathcal F_0\cup\bigcup_i\mathcal G_i$ with the pieces pairwise disjoint; each $\mathcal G_i$ comes with its own $k$-partition and pattern.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 7, Theorem 3.9

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Theorem 3.9, p. 7 (the canonical partition). -/
theorem theorem_3_9 (k ℓ s : ℕ) (hk : 4 ≤ k) (hℓ : 1 ≤ ℓ) (hs : k * ℓ ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (𝓕 : Finset (Finset (Fin n))),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k → ¬ ContainsLinearPath 𝓕 ℓ →
      ∃ (m : ℕ) (G : Fin m → Finset (Finset (Fin n))) (F₀ : Finset (Finset (Fin n))),
        𝓕 = F₀ ∪ univ.biUnion G ∧ (∀ i, Disjoint (G i) F₀) ∧
        Pairwise (fun i j => Disjoint (G i) (G j)) ∧
        (∀ i, ∃ (χ : Fin n → Fin k) (J : Finset (Finset (Fin k))),
          IsHomogeneous s (G i) χ J ∧ rank J = k - 1 ∧ IsType1 J) ∧
        (#F₀ : ℝ) ≤ (n.choose (k - 2) : ℝ) / c := by sorry

end LinearPathTuran.Exact
