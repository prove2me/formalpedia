-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_5
-- name    : MinKCutII.Main.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:03.697755+00:00
-- url     : https://prove2.me/theorems/5f0ad830-eaab-4245-8026-8a44c027b610
-- title:
--   Lemma 5 — at most one cut bipartition has value below λ₃/2
-- statement:
--   Let $G=(V,E,c)$ be connected with positive capacities and $n\ge3$, and let $\lambda=\lambda_3(G)$ (a real number since $n\ge3$). If $S,T$ are cuts ($\emptyset\ne S,T\subsetneq V$) with
--   $$c_G(S)<\frac{\lambda}{2},\qquad c_G(T)<\frac{\lambda}{2},$$
--   then $\{S,V\setminus S\}=\{T,V\setminus T\}$: there is at most one strict-small cut bipartition.
--
--   The uniqueness lets the 3-cut algorithm identify a strict-small optimum side with one global minimum cut computation.
--
--   Differences from the source:
--
--   - reading: S, T ⊊ V → S, T cuts: nonempty proper subsets; reason: a cut S ⊊ V of Definition 2 is a proper nonempty side; with S = ∅ (c_G(∅) = 0) the claim would fail whenever a strict-small cut exists
--   - encoding: equality of unordered pairs {S, V \ S} = {T, V \ T} → equality in Sym2 (Finset V); reason: Sym2 is the type of unordered pairs
--   - encoding: λ = λ₃(G) → a real L with lam G 3 = L; reason: λ₃ is finite since n ≥ 3
--   - generalization: positive integer capacities → positive real capacities; reason: the statement holds for real capacities; integers are a special case
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 8, Lemma 5

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-- **Lemma 5** (p. 8). In a connected graph with positive capacities and `n ≥ 3` vertices, with
`λ = λ_3(G)`: if `S, T` are cuts with `c_G(S), c_G(T) < λ/2`, then the bipartitions agree:
`{S, V \ S} = {T, V \ T}`. -/
theorem lemma_5 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E)
    (hpos : PosCap G) (hconn : IsConnected G) (hn : 3 ≤ Fintype.card V) (L : ℝ)
    (hL : lam G 3 = (L : WithTop ℝ)) (S T : Finset V) (hS : IsCut S) (hT : IsCut T)
    (hSv : cutVal G S < L / 2) (hTv : cutVal G T < L / 2) :
    s(S, Finset.univ \ S) = s(T, Finset.univ \ T) := by sorry

end MinKCutII.Main
