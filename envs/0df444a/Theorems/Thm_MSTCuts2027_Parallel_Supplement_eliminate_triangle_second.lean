-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_Supplement_eliminate_triangle_second
-- name    : MSTCuts2027.Parallel.Supplement.eliminate_triangle_second
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:38:57.469745+00:00
-- url     : https://prove2.me/theorems/ea67faaf-31b4-4f8f-9b5c-e8fb294a7bfe
-- title:
--   Lemma 9 — Algorithm 5 reports the least $G_2$ edge of a triangle in $O(1)$ (corrected: return branches of Algorithm 5)
-- statement:
--   There is a constant $c$ such that the following holds for every $n$, every symmetric real cut function $F$ on $n$ vertices for which every pair of distinct vertices has a second mincut, and all memory contents of the machine. Let $u,v,x$ be vertices with $x\notin\{u,v\}$ and
--   $$\lambda_1(u,v)\ge\lambda_1(x,u)=\lambda_1(x,v).$$
--   Let the memory hold a $(u,v)$-mincut $C^1_{u,v}$ and a second $(u,v)$-mincut $C^2_{u,v}$ as Boolean arrays, and the values $\lambda_1(u,v)$, $\lambda_1(x,u)$ in two real cells. Then Algorithm 5 halts with work and depth at most $c$ and writes a vertex $a$, with $b$ the other element of $\{u,v\}$, such that $(x,a)$ is a least-capacity edge of the triangle on $u,v,x$ in $G_2$:
--   $$\lambda_2(x,a)\le\lambda_2(x,b),\qquad \lambda_2(x,a)\le\lambda_2(u,v).$$
--
--   Ties are allowed. The lemma is the constant-time step of the pruning procedure of Lemma 10.
--
--   Differences from the source:
--   - correction: Algorithm 5 lines 3 and 5 return (x,u) when x ∈ C → the program returns the edge from x to the endpoint the tested cut separates from x; reason: with u ∈ C (footnote 2), V = {u,v,x}, F({u}) = F({v,x}) = 3, F({v}) = F({u,x}) = 2, F({x}) = F({u,v}) = 1 is Type 1 with the (u,v)-mincut {u,x} containing x, and λ2(x,v) = 2 < λ2(x,u) = 3, so the printed line 3 returns (x,u), which is not least
--   - encoding: O(1) time → explicit constant c fixed before the instance, bounding work and depth of the run in the published machine; reason: the paper gives no numerical constant
--   - encoding: the test x ∈ C on a cut containing u → the memberships of x and u are compared; reason: the cut (C, V∖C) is unoriented; on a cut containing u both tests agree
--   - encoding: inputs C¹, C² and the λ1 values read in lines 2 and 4 → pointers to Boolean arrays and two real cells, passed as arguments; reason: this is how the machine accesses the cut store and the mincut values
--   - encoding: least capacity edge → λ2(x,a) at most both other capacities, ties allowed; reason: same statement
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 9 and Algorithm 5, printed p. 13, PDF p. 15

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondAlgorithms

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-- Lemma 9: Algorithm 5 (return branches corrected) runs in constant work and depth and reports
`a ∈ {u, v}` such that `(x, a)` is a least-capacity edge of the triangle `u, v, x` in `G₂`. -/
theorem eliminate_triangle_second :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      SecondMincutsExist F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (u v x : Fin n) (p₁ p₂ ruv rxu dest : ℕ),
        IsReady n σ → p₁ + n ≤ wordBound n → p₂ + n ≤ wordBound n →
        ruv ≤ wordBound n → rxu ≤ wordBound n → dest ≤ wordBound n →
        IsMincut F u v (cutAt n σ.mem p₁) → IsSecondMincut F u v (cutAt n σ.mem p₂) →
        σ.rmem ruv = lam F u v → σ.rmem rxu = lam F x u →
        x ≠ u → x ≠ v → lam F x u ≤ lam F u v → lam F x u = lam F x v →
        ∃ o : Outcome ℝ,
          Halts (machine P) elim2Program 0
            [((x : ℕ) : ℤ), ((u : ℕ) : ℤ), ((v : ℕ) : ℤ), (p₁ : ℤ), (p₂ : ℤ), (ruv : ℤ),
              (rxu : ℤ), (dest : ℤ)] σ o ∧
          o.work ≤ c ∧ o.depth ≤ c ∧
          ∃ a b : Fin n, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
            o.store.mem dest = ((a : ℕ) : ℤ) ∧
            lam2 F x a ≤ lam2 F x b ∧ lam2 F x a ≤ lam2 F u v := by sorry

end MSTCuts2027.Parallel.Supplement
