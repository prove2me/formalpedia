-- Prove2me | Theorems.Thm_LooseHamHitting_Main_lemma_3_3
-- name    : LooseHamHitting.Main.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:01.320752+00:00
-- url     : https://prove2.me/theorems/05138905-451f-415d-8002-0926ceddc364
-- title:
--   Lemma 3.3 — exact count of mixed Hamilton cycles in the complete 3-graph, the M-compatible ratio, and the first moment in a uniform m-edge 3-graph
-- statement:
--   Let $M$ be a matching of $s\ge1$ pairs on an $n$-vertex set $V$, with $n-s$ even and $n\ge\max\{s+6,3s\}$.
--
--   (i) $$\Phi\Big(\binom V3,M\Big)=\frac{2^{s-1}(n-2s)!\,\big(\frac{n-s-2}2\big)!}{\big(\frac{n-3s}2\big)!}.$$
--
--   (ii) If $n\ge5s$, then with $K_M=\{e\in\binom V3:|e\cap V(M)|\le1\}$,
--   $$\frac{\Phi(K_M,M)}{\Phi(\binom V3,M)}=\frac{\big(\frac{n-3s}2\big)!\big(\frac{n-3s-2}2\big)!}{\big(\frac{n-s-2}2\big)!\big(\frac{n-5s}2\big)!}\ \ge\ 1-\frac{2s(s-1)}{n-s-2}.$$
--
--   (iii) For $0\le m\le\binom n3$ and $G$ uniform among the $m$-edge 3-graphs on $V$,
--   $$E[\Phi(G,M)]=\Phi\Big(\binom V3,M\Big)\binom{m}{(n-s)/2}\Big/\binom{\binom n3}{(n-s)/2},$$
--   and the same identity holds with both cycle numbers restricted to $K_M$ ($E[\Phi(G\cap K_M,M)]=\Phi(K_M,M)\cdot$ the same ratio). There are an absolute $K>0$ and $N$ such that whenever moreover $n\ge N$, $s\le n^{1/10}$ and $|m-n\log n/3|\le n\log\log n$,
--   $$\Big|\log E[\Phi(G,M)]-\Big(\frac{n-s}2\log\frac{6m}n-n+s\Big)\Big|\le K\frac n{\log n},$$
--   and the same bound holds for $E[\Phi(G\cap K_M,M)]$.
--
--   This is the first-moment benchmark that Theorem 4.3 matches up to $\exp\{O(n/\log n)\}$.
--
--   Differences from the source:
--   - encoding: log E[Φ(G, M)] = ((n − s)/2) log(6m/n) − n + s + O(n/log n) as n → ∞ → ∃ K > 0, ∃ N, for every instance with n ≥ N meeting the hypotheses, |log E − main term| ≤ K n/log n; reason: explicit quantification of O(·) as n → ∞, uniform over the instances
--   - encoding: cycles whose triples contain at most one vertex of V(M) → cycles of G ∩ K_M, with K_M = compatibleTriples V M; reason: the same family of cycles
--   - encoding: expectation over a uniform m-edge 3-graph → average over all m-subsets of the triples of V (expectedPhi); reason: definition of the uniform law
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, pp. 8–9, Lemma 3.3

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy
import Definitions.Def_LooseHamHitting_Main_Marginals

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Lemma 3.3: the number of mixed Hamilton cycles in the complete 3-graph, the restriction ratio
to `M`-compatible triples, and the first moment in the uniform `m`-edge 3-graph. -/
theorem lemma_3_3 :
    (∀ (β : Type*) (V : Finset β) (M : Finset (Finset β)) (n s : ℕ),
      V.card = n → M.card = s → IsMatching V M → 1 ≤ s → Even (n - s) →
      s + 6 ≤ n → 3 * s ≤ n →
      ((Phi V (V.powersetCard 3) M : ℝ) =
          (2 : ℝ) ^ (s - 1) * ((n - 2 * s).factorial : ℝ) * (((n - s - 2) / 2).factorial : ℝ) /
            (((n - 3 * s) / 2).factorial : ℝ)) ∧
      (5 * s ≤ n →
        (Phi V (compatibleTriples V M) M : ℝ) / (Phi V (V.powersetCard 3) M : ℝ) =
            (((n - 3 * s) / 2).factorial : ℝ) * (((n - 3 * s - 2) / 2).factorial : ℝ) /
              ((((n - s - 2) / 2).factorial : ℝ) * (((n - 5 * s) / 2).factorial : ℝ)) ∧
          1 - 2 * (s : ℝ) * ((s : ℝ) - 1) / ((n : ℝ) - s - 2) ≤
            (Phi V (compatibleTriples V M) M : ℝ) / (Phi V (V.powersetCard 3) M : ℝ)) ∧
      (∀ m : ℕ, m ≤ n.choose 3 →
        expectedPhi V (V.powersetCard 3) M m =
            (Phi V (V.powersetCard 3) M : ℝ) * ((m.choose ((n - s) / 2) : ℕ) : ℝ) /
              (((n.choose 3).choose ((n - s) / 2) : ℕ) : ℝ) ∧
          expectedPhi V (compatibleTriples V M) M m =
            (Phi V (compatibleTriples V M) M : ℝ) * ((m.choose ((n - s) / 2) : ℕ) : ℝ) /
              (((n.choose 3).choose ((n - s) / 2) : ℕ) : ℝ))) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ (β : Type*) (V : Finset β) (M : Finset (Finset β)) (n s m : ℕ),
        V.card = n → M.card = s → IsMatching V M → 1 ≤ s → Even (n - s) →
        s + 6 ≤ n → 3 * s ≤ n → m ≤ n.choose 3 → N ≤ n →
        (s : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) →
        |(m : ℝ) - (n : ℝ) * Real.log n / 3| ≤ (n : ℝ) * Real.log (Real.log n) →
        |Real.log (expectedPhi V (V.powersetCard 3) M m) -
            (((n : ℝ) - s) / 2 * Real.log (6 * (m : ℝ) / n) - n + s)| ≤ K * n / Real.log n ∧
          |Real.log (expectedPhi V (compatibleTriples V M) M m) -
            (((n : ℝ) - s) / 2 * Real.log (6 * (m : ℝ) / n) - n + s)| ≤ K * n / Real.log n) := by sorry

end LooseHamHitting.Main
