-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_4_7
-- name    : MildHamilton.Main.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:52.825235+00:00
-- url     : https://prove2.me/theorems/b0755cd9-eb4d-4588-a3b5-01b4efdd38d6
-- title:
--   Lemma 4.7, p. 10 — random subsets of expanders contain Hamilton routers
-- statement:
--   There exist absolute constants $c>0$, $K>1$ and $n_0$ such that the following holds. Let $H$ be an $(n,d,\lambda)$-graph with $n\ge n_0$ and $\lambda\le(1-\delta)d$ for some $0<\delta\le1/2$. Let $0<q\le\delta/100$ with $qn\in2\mathbb N$, and suppose $qd\ge K\delta^{-4}(\log n)^2$. Let $R\subseteq V(H)$ be chosen uniformly among the $qn$-element subsets of $V(H)$. Then with probability at least $1-1/n$, the following holds simultaneously for all disjoint sets $A,B\subseteq V(H)\setminus R$ with $|A|=|B|=k$:
--
--   if every $x\in A\cup B$ satisfies $d_H(x,R)\ge qd/2$, every $v\in R$ satisfies
--
--   $$d_H(v,A\cup B)\le\frac{c\,\delta^3qd}{\log n},$$
--
--   and $k\le c\delta^3|R|(\log n)^{-2}$, then $H[A\cup B\cup R]$ contains an $A,B$-Hamilton router $S$ with $A\cup B\subseteq V(S)\subseteq A\cup B\cup R$.
--
--   The event depends on $R$ alone. This is the step of the final proof that places the router inside the reservoir.
--
--   Differences from the source:
--   - encoding: all non-trivial eigenvalues of the adjacency matrix have absolute value at most λ → the published ExplicitExpanders.Attach.IsNDLambda: every eigenvalue with an eigenvector orthogonal to the all-ones vector; reason: for a d-regular graph the all-ones vector spans an eigenline for the top eigenvalue, so the eigenvalues on its orthogonal complement are the spectrum with one copy of d removed; multiplicity counts, and a disconnected graph keeps a second copy of d
--   - encoding: probability under a uniform choice → counting in multiplied form, #event against x · #sample (UniformProbLE / UniformProbGE); reason: the quotient would be 0/0 on an empty sample space; on a nonempty one the two forms are equivalent
--   - encoding: qn ∈ 2ℕ, R among the qn-element subsets → a natural number j with qn = 2j, R among the 2j-element subsets; reason: the same sets
--   - encoding: H[A ∪ B ∪ R] contains a router S → a vertex set W between A ∪ B and A ∪ B ∪ R with IsHamiltonRouter H.Adj W A B; reason: a router S inside H on vertex set W is a router for H.Adj on W, and conversely H[W] is then a router; only the vertex set of S matters
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 4.7, p. 10

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_MildHamilton_Main_Spectral
import Definitions.Def_MildHamilton_Main_Router

namespace MildHamilton.Main

open Classical in
/-- Lemma 4.7 (Muyesser, STOC 2027 submission #233, p. 10): random subsets of expanders contain Hamilton
routers. `qn = 2j`, and `R` is uniform among the `qn`-element subsets of `V(H)`; the event, about `R` alone,
quantifies over all disjoint `A`, `B` inside `V(H) \ R` with `|A| = |B|`. The router `S` lives on a vertex set `W`
with `A ∪ B ⊆ W ⊆ A ∪ B ∪ R`, with the edges of `H`. -/
theorem lemma_4_7 :
    ∃ (c K : ℝ) (n₀ : ℕ), 0 < c ∧ 1 < K ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
        (n d : ℕ) (lam δ q : ℝ) (j : ℕ),
        ExplicitExpanders.Attach.IsNDLambda H n d lam → n₀ ≤ n → lam ≤ (1 - δ) * d → 0 < δ → δ ≤ 1 / 2 →
        0 < q → q ≤ δ / 100 → q * n = 2 * (j : ℝ) →
        K * δ ^ (-4 : ℤ) * Real.log n ^ 2 ≤ q * d →
        UniformProbGE (Finset.powersetCard (2 * j) (Finset.univ : Finset V))
          (fun R => ∀ A B : Finset V, Disjoint A B → Disjoint A R → Disjoint B R →
            A.card = B.card →
            (∀ x ∈ A ∪ B, q * d / 2 ≤ (nbrCount H x R : ℝ)) →
            (∀ v ∈ R, (nbrCount H v (A ∪ B) : ℝ) ≤ c * δ ^ 3 * q * d / Real.log n) →
            (A.card : ℝ) ≤ c * δ ^ 3 * (R.card : ℝ) * (Real.log n) ^ (-2 : ℤ) →
            ∃ W : Finset V, A ∪ B ⊆ W ∧ W ⊆ A ∪ B ∪ R ∧ IsHamiltonRouter H.Adj W A B)
          (1 - 1 / (n : ℝ)) := by sorry

end MildHamilton.Main
