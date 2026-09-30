-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_iterate_invariants
-- name    : MarkovChainChoice.DimReduction.iterate_invariants
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:14.494384+00:00
-- url     : https://prove2.me/theorems/ff37d887-9f24-46ef-82f9-350e30fd18cc
-- title:
--   Section 7 — the iterates of Dimension Reduction stay in $\mathcal H$ and their supports shrink
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions, let $(\hat x,\hat z)\in\mathcal H$, and run the Dimension Reduction algorithm from $(x^1,z^1)=(\hat x,\hat z)$. Let $k\ge1$ be an iteration reached by the algorithm, i.e. the algorithm did not stop at any iteration $l$ with $1\le l<k$. Then
--
--   1. $(x^k,z^k)\in\mathcal H$;
--   2. if the algorithm does not stop at iteration $k$ either, then for every $j^k\in S^k$ attaining $\alpha^k=\min\{x^k_j/P_{j,S^k}: j\in S^k\}$,
--   $$
--   S^{k+1}\subseteq S^k\setminus\{j^k\}.
--   $$
--
--   These invariants give the termination bound and the nesting of the offer sets in Theorem 9.
--
--   **Formalization Note** The paper states the induction for $(\hat x,\hat z)$ the optimal solution of (Reduced), using only that it lies in $\mathcal H$; the statement here assumes $(\hat x,\hat z)\in\mathcal H$, which every feasible solution of (Reduced) satisfies. "Stops at iteration $l$" means $S^l=\emptyset$ (Step 1) or $\alpha^l=1$ (Step 2).
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1333–1334, Section 7, paragraph after the Dimension Reduction algorithm

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem iterate_invariants {n : ℕ} (M : Model n) (x z : Fin n → ℝ) (hxz : (x, z) ∈ H M)
    (k : ℕ) (hk : 1 ≤ k) (hrun : ∀ l, 1 ≤ l → l < k → ¬ drStops M x z l) :
    drIter M x z k ∈ H M ∧
      (¬ drStops M x z k → ∀ j ∈ drS M x z k,
        (drIter M x z k).1 j / purchase M (drS M x z k) j = drA M x z k →
        drS M x z (k + 1) ⊆ (drS M x z k).erase j) := by sorry

end MarkovChainChoice.DimReduction
