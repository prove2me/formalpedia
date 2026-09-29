-- Prove2me | Theorems.Thm_KServer_workFnU_dual_quasiconvex
-- name    : KServer.workFnU_dual_quasiconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:44:53.492361+00:00
-- url     : https://prove2.me/theorems/b9fdd12e-850d-4a0f-9b66-187d937d516b
-- title:
--   The dual functional of the work function is quasiconvex with the same alignment
-- statement:
--   Fix a point $s$ and consider the **dual functional** of a $k$-server work function $w$,
--
--   $$F(X) \;=\; w(X) - d(X, s^k) \;=\; w(X) - \sum_{i} d(x_i, s),$$
--
--   the object at the heart of the Koutsoupias--Papadimitriou duality lemma: its minimisers are where the extended cost of a request at $s$ is realised, and its minima drive the potential of Coester and Koutsoupias. The theorem says $F$ is **quasiconvex in the same pairing sense as $w$ itself, with the same alignment**: for any two configurations $X, Y$ there is a permutation $\pi$ such that for *every* split of the coordinates into two blocks, the two hybrid configurations $H_1, H_2$ (taking one block from $X$ and the complementary block from $Y \circ \pi$, and vice versa) satisfy
--
--   $$F(H_1) + F(H_2) \;\le\; F(X) + F(Y).$$
--
--   ## Why it is free
--
--   Quasiconvexity is a genuine theorem for $w$ --- it encodes the exchange structure of optimal offline solutions. For the dual functional no new argument is needed, because the subtracted term is **modular**: $d(X, s^k)$ is a sum of per-coordinate distances, and each coordinate of $X$ and of $Y \circ \pi$ appears in exactly one of the two hybrids. Hence
--
--   $$d(H_1, s^k) + d(H_2, s^k) = d(X, s^k) + d(Y, s^k)$$
--
--   exactly (after re-indexing the $Y$-part along $\pi$, under which the sum is invariant), and subtracting this identity from the quasiconvexity of $w$ gives the claim --- with the *same* $\pi$, which is what makes the lemma directly usable: any exchange argument for $w$ runs verbatim for $F$.
--
--   ## Role
--
--   In the tree analysis of Coester and Koutsoupias, the anchors of the potential are located greedily with respect to dual functionals: their Lemma 25 finds the first anchor among the minimisers of $x \mapsto w(x\,x_2\dots x_k) - d(x, x_2)$, an instance of minimising $F$ under a containment constraint, and the greedy and substitution lemmas that justify such choices are exchange arguments of exactly the pairing form above. This theorem is what licenses running them against $F$ rather than $w$.
--
--   ## Formalization note
--
--   Configurations are functions $\mathrm{Fin}\,k \to M$ and the hybrids are written with an `if i ∈ t` selector over a `Finset (Fin k)`; $w$ is `workFnU`, the work function of the unlabelled configuration. The statement quantifies the split *inside* the existential, exactly as in the underlying `workFnU_quasiconvex`, so a single alignment witnesses all splits at once.
-- source:
--   Implicit in C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, proof of Lemma 25 (quasiGreedy applied to X ↦ w(X) − d(X, x₂²)); quasiconvexity and the dual functional are from E. Koutsoupias, C. H. Papadimitriou, 'On the k-server conjecture', JACM 42 (1995).

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_dual_quasiconvex (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (s : M) (X Y : Config k M) :
    ∃ π : Equiv.Perm (Fin k), ∀ t : Finset (Fin k),
      (workFnU C₀ σ (fun i => if i ∈ t then X i else Y (π i))
          - ∑ i, dist s ((fun i => if i ∈ t then X i else Y (π i)) i))
        + (workFnU C₀ σ (fun i => if i ∈ t then Y (π i) else X i)
          - ∑ i, dist s ((fun i => if i ∈ t then Y (π i) else X i) i))
      ≤ (workFnU C₀ σ X - ∑ i, dist s (X i))
        + (workFnU C₀ σ Y - ∑ i, dist s (Y i)) := by sorry

end KServer
