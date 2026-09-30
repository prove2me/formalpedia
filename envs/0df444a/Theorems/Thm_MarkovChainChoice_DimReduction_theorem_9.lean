-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_theorem_9
-- name    : MarkovChainChoice.DimReduction.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:48.037764+00:00
-- url     : https://prove2.me/theorems/65a70905-244f-4341-84aa-bb5afbaba1af
-- title:
--   Theorem 9 — Dimension Reduction writes the (Reduced) optimum as a convex combination of at most $n+1$ nested (Balance) solutions
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions, let network data $T$, $c$, $a$, $r$ be given, and let $(\hat x,\hat z)$ be an optimal solution of the (Reduced) linear program. Run the Dimension Reduction algorithm from $(x^1,z^1)=(\hat x,\hat z)$, producing subsets $S^1,S^2,\dots$ and scalars $\alpha^1,\alpha^2,\dots$, and let
--   $$
--   \gamma^k=(1-\alpha^1)\cdots(1-\alpha^{k-1})\,\alpha^k .
--   $$
--   Then:
--
--   1. the algorithm stops, and it does so after at most $n+1$ iterations: its first stopping iteration $K$ satisfies $1\le K\le n+1$;
--   2. if the algorithm stops at iteration $K$ (and not before), then
--   $$
--   \hat x=\sum_{k=1}^K\gamma^kP_{S^k},\qquad \hat z=\sum_{k=1}^K\gamma^kR_{S^k},\qquad \sum_{k=1}^K\gamma^k=1,
--   $$
--   and the generated subsets are nested: $S^1\supseteq S^2\supseteq\cdots\supseteq S^K$.
--
--   Combined with the equivalence of the (Reduced) and (Choice Based) linear programs, this shows that an optimal solution of the (Choice Based) program can be recovered from the (Reduced) optimum and randomizes over at most $n+1$ nested offer sets.
--
--   **Formalization Note** "The algorithm stops at iteration $K$" is the first $K$ with $S^K=\emptyset$ or $\alpha^K=1$; iterates after it are never referenced. The paper writes $\supset$ for (not necessarily strict) inclusion.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1334, Theorem 9

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_Reduced
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem theorem_9 {n m : ℕ} (M : Model n) (T : ℕ) (c : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (r : Fin n → ℝ) (x z : Fin n → ℝ) (hopt : IsReducedOptimal M T c a r x z) :
    (∃ K, 1 ≤ K ∧ K ≤ n + 1 ∧ drStops M x z K ∧ ∀ k, 1 ≤ k → k < K → ¬ drStops M x z k) ∧
    ∀ K, 1 ≤ K → drStops M x z K → (∀ k, 1 ≤ k → k < K → ¬ drStops M x z k) →
      x = ∑ k ∈ Finset.Icc 1 K, drGamma M x z k • purchase M (drS M x z k) ∧
      z = ∑ k ∈ Finset.Icc 1 K, drGamma M x z k • visitNot M (drS M x z k) ∧
      ∑ k ∈ Finset.Icc 1 K, drGamma M x z k = 1 ∧
      ∀ k, 1 ≤ k → k < K → drS M x z (k + 1) ⊆ drS M x z k := by sorry

end MarkovChainChoice.DimReduction
