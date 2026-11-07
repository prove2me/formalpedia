-- Prove2me | Theorems.Thm_GenTuranHard_ineq_4_11
-- name    : GenTuranHard.ineq_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:30.718212+00:00
-- url     : https://prove2.me/theorems/ddb9419f-7779-4b3f-b68f-36146c1008c5
-- title:
--   Inequality (4.11) — $0 \le \hom(T,A) - \gamma N(A,T) \le v(T)^2 N^{v(T)-1}$
-- statement:
--   Let $T$ be a graph and $\gamma$ its number of automorphisms, so each copy of $T$ corresponds to exactly $\gamma$ injective homomorphisms. Then for any $N$-vertex graph $A$,
--
--   $$
--   0 \le \hom(T, A) - \gamma\, N(A, T) \le v(T)^2 N^{v(T) - 1}.
--   $$
--
--   It converts the homomorphism bounds of Lemmas 4.7–4.9 into bounds on copy counts, hence on $\mathrm{ex}$ and $\mathrm{ex}'$.
--
--   **Formalization Note** $\gamma$ is the number of graph isomorphisms of $T$ onto itself; the exponent $v(T) - 1$ is a natural number.
--
--   Differences from the source:
--   - generalization: T the bipartite graph of §4 (e(T) > 0, v(T) ≥ 3) → every finite graph T; reason: the counting argument uses no property of T; the source's T is a special case
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Inequality (4.11), pp.20–21

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Inequality (4.11)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, (4.11),
pp.20–21). Let `γ` be the number of automorphisms of `T`, so each copy of `T` corresponds to exactly `γ`
injective homomorphisms. Then for any `N`-vertex graph `A`,
`0 ≤ hom(T, A) − γ·N(A, T) ≤ v(T)²·N^{v(T)−1}`.

**Formalization Note** Stated for every finite graph `T`. `γ = |Aut(T)|` is the number of graph
isomorphisms `T ≃g T`; `N(A, T)` is `copyCount`. The exponent `v(T) − 1` is a natural number. -/
theorem ineq_4_11 {W V : Type} [Fintype W] [Fintype V] (T : SimpleGraph W) (A : SimpleGraph V) :
    ((Nat.card (T ≃g T) : ℝ) * (A.copyCount T : ℝ) ≤ (homCount T A : ℝ)) ∧
      (homCount T A : ℝ) - (Nat.card (T ≃g T) : ℝ) * (A.copyCount T : ℝ) ≤
        (Fintype.card W : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (Fintype.card W - 1) := by sorry

end GenTuranHard
