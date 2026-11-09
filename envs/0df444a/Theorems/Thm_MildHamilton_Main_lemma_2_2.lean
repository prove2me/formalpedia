-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_2_2
-- name    : MildHamilton.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:57.121804+00:00
-- url     : https://prove2.me/theorems/4098d4d9-6982-4ad4-9c94-146b5c52eaad
-- title:
--   Lemma 2.2, p. 3 — expansion inheritance under vertex subsampling
-- statement:
--   For every $a>0$ let $C_a=30000(a+4)$. Let $G$ be an $(n,d,\lambda)$-graph with adjacency matrix $A$ and $\lambda\le(1-\delta)d$. Let $m\ge2$ be an integer, set $p=m/n$ and $D=pd$, and assume $p\le\delta/100$ and $D\ge C_a\delta^{-2}\log n$. Choose $(U,V)$ uniformly among all ordered pairs of disjoint $m$-subsets of $V(G)$, and let $K=A[U,V]$. Then with probability at least $1-n^{-a}$,
--
--   $$s_2(K)\le\Big(1-\frac\delta2\Big)D.$$
--
--   So a random pair of sets of density $p$ keeps a one-sided spectral gap, and hence cut density through Lemma 2.1, at the cost of half the gap. This lets the final proof work with random layers of the host graph.
--
--   Differences from the source:
--   - encoding: all non-trivial eigenvalues of the adjacency matrix have absolute value at most λ → the published ExplicitExpanders.Attach.IsNDLambda: every eigenvalue with an eigenvector orthogonal to the all-ones vector; reason: for a d-regular graph the all-ones vector spans an eigenline for the top eigenvalue, so the eigenvalues on its orthogonal complement are the spectrum with one copy of d removed; multiplicity counts, and a disconnected graph keeps a second copy of d
--   - encoding: probability under a uniform choice → counting in multiplied form, #event against x · #sample (UniformProbLE / UniformProbGE); reason: the quotient would be 0/0 on an empty sample space; on a nonempty one the two forms are equivalent
--   - encoding: δ with p ≤ δ/100 → the explicit hypothesis 0 < δ; reason: implied by p ≤ δ/100 and m ≥ 2 once n ≥ 1; at n = 0 there is no disjoint pair of m-subsets
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 2.2, p. 3, eq. (1)

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

open Classical in
/-- Lemma 2.2 (Muyesser, STOC 2027 submission #233, p. 3): expansion inheritance under vertex subsampling,
with `C_a = 30000 (a + 4)`, `p = m / n` and `D = p d`. `(U, W)` is uniform among the ordered pairs of
disjoint `m`-subsets of `V(G)`, and `K = A[U, W]`. -/
theorem lemma_2_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d m : ℕ) (lam δ a : ℝ) (ha : 0 < a) (hG : ExplicitExpanders.Attach.IsNDLambda G n d lam) (hδ : 0 < δ)
    (hlam : lam ≤ (1 - δ) * d) (hm : 2 ≤ m) (hp : (m : ℝ) / n ≤ δ / 100)
    (hD : 30000 * (a + 4) * δ ^ (-2 : ℤ) * Real.log n ≤ (m : ℝ) / n * d) :
    UniformProbGE
      (((Finset.powersetCard m (Finset.univ : Finset V)) ×ˢ
        (Finset.powersetCard m (Finset.univ : Finset V))).filter fun UW => Disjoint UW.1 UW.2)
      (fun UW => secondSingularValue (biadjacency G UW.1 UW.2) ≤ (1 - δ / 2) * ((m : ℝ) / n * d))
      (1 - (n : ℝ) ^ (-a)) := by sorry

end MildHamilton.Main
