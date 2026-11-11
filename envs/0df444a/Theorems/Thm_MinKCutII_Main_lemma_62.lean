-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_62
-- name    : MinKCutII.Main.lemma_62
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:23.809353+00:00
-- url     : https://prove2.me/theorems/73db2747-9d8b-4477-9810-375fc5ce19b3
-- title:
--   Lemma 62 — for k ≥ 5 some support tree of a sparsifier's k-cut packing (k − 2)-respects a light cut
-- statement:
--   Let $F=(V,E,c)$ be connected with positive capacities and $5\le k\le|V|$. Let $H$ be a $(1\pm\tfrac1{100})$-spectral sparsifier of $F$ (Definition 59), and let $(y,z)$ be tree weights and slacks in $H$ satisfying (1) and (2) of Lemma 43 with $\eta=1/100$; let $D_k=\{T: y_T>0\}$ be the support. If $S$ is a cut with $c_F(S)\le2\lambda_k(F)/k$, then some $T\in D_k$ satisfies
--   $$|\delta_T(S)|\le k-2.$$
--   It replaces random tree sampling in the deterministic reduction for $k\ge5$.
--
--   Differences from the source:
--
--   - generalization: D_k the full support of the packing of Lemma 43 computed in the spectral sparsifier H → the support of every (y, z) in every (1 ± 1/100)-spectral sparsifier H of F satisfying (1) and (2) with η = 1/100; reason: the proof uses only spectral approximation and (1), (2); the paper's H and packing are one instance
--   - reading: Let k ≥ 5 (F the connected graph of §6.4; Lemma 43 needs k ≤ n) → F connected, 5 ≤ k ≤ |V|; reason: §6.4: all calls are on connected graphs; Lemma 43 assumes k ≤ n
--   - reading: c_F(S) ≤ 2λ_k(F)/k → S a cut (nonempty, proper) with that bound; reason: S is a side of a cut
--   - generalization: positive integer capacities of F, rational of H → positive real capacities; reason: special cases
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 44, Lemma 62 (with §6.3: ε = η = 1/100, D_k the full support)

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts
import Definitions.Def_MinKCutII_Main_TreePacking
import Definitions.Def_MinKCutII_Main_Sparsifier

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-- **Lemma 62** (p. 44), for every packing satisfying (1)–(2) of Lemma 43. Let `F` be connected with
positive capacities, `5 ≤ k ≤ |V|`, `H` a `(1 ± 1/100)`-spectral sparsifier of `F`, and `(y, z)`
tree weights and slacks in `H` satisfying (1) and (2) with `η = 1/100`; let `D_k` be the support of
`y`. If `S` is a cut with `c_F(S) ≤ 2λ_k(F)/k`, some `T ∈ D_k` has `|δ_T(S)| ≤ k − 2`. -/
theorem lemma_62 {V E E' : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype E']
    (F : CapGraph V E) (H : CapGraph V E') (k : ℕ) (y : Finset E' → ℝ) (z : E' → ℝ)
    (S : Finset V) (hpos : PosCap F) (hconn : IsConnected F) (hk : 5 ≤ k)
    (hkn : k ≤ Fintype.card V) (hH : IsSpectralSparsifier H F (1 / 100))
    (hpack : IsKCutPacking H k (1 / 100) y z) (hS : IsCut S)
    (hlight : ∃ L : ℝ, lam F k = (L : WithTop ℝ) ∧ cutVal F S ≤ 2 * L / k) :
    ∃ T : Finset E', 0 < y T ∧ (treeDelta H T S).card ≤ k - 2 := by sorry

end MinKCutII.Main
