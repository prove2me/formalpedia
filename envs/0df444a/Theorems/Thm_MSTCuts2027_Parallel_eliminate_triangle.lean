-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_eliminate_triangle
-- name    : MSTCuts2027.Parallel.eliminate_triangle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:35.28875+00:00
-- url     : https://prove2.me/theorems/d1b11e7c-776c-4749-868f-c661b81e2592
-- title:
--   Lemma 5 — EliminateTriangle runs in $O(1)$ and reports the least edge of the triangle
-- statement:
--   There is a constant $c$ such that the following holds for every symmetric real cut function $F$ on $n$ vertices and all memory contents of the machine. Let $x\notin\{u,v\}$ and let the array at address $p$ be a $(u,v)$-mincut $C$. Algorithm 1 halts with work and depth at most $c$, reporting a vertex $a$, with $b$ the other element of $\{u,v\}$, such that:
--
--   1. $C$ is an $(x,a)$-mincut, or every $(x,b)$-mincut is an $(x,a)$-mincut;
--   2. $(x,a)$ is a least-capacity edge of the triangle on $u,v,x$ in $G_1$:
--   $$\lambda_1(x,a)\le\lambda_1(x,b),\qquad \lambda_1(x,a)\le\lambda_1(u,v).$$
--
--   Ties are allowed, so "the" least edge means a least edge.
--
--   Differences from the source:
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - encoding: EliminateTriangle tests x ∈ C for a cut whose orientation contains u → the test compares the memberships of x and u; reason: the cut (C, V∖C) is unoriented; on a cut containing u both tests agree
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 5, printed p. 7, PDF p. 9

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 5: Algorithm 1 runs in constant work and depth and reports `a` with the two properties. -/
theorem eliminate_triangle :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (P : Oracle ℝ n) (σ : Store ℝ) (u v x : Fin n) (p dest : ℕ),
        IsReady n σ → p + n ≤ wordBound n → dest ≤ wordBound n →
        IsMincut F u v (cutAt n σ.mem p) → x ≠ u → x ≠ v →
        ∃ o : Outcome ℝ,
          Halts (machine P) algorithms Prog.pElim
            [((x : ℕ) : ℤ), ((u : ℕ) : ℤ), ((v : ℕ) : ℤ), (p : ℤ), (dest : ℤ)] σ o ∧
          o.work ≤ c ∧ o.depth ≤ c ∧
          ∃ a b : Fin n, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
            o.store.mem dest = ((a : ℕ) : ℤ) ∧
            (IsMincut F x a (cutAt n σ.mem p) ∨ ∀ D, IsMincut F x b D → IsMincut F x a D) ∧
            lam F x a ≤ lam F x b ∧ lam F x a ≤ lam F u v := by sorry

end MSTCuts2027.Parallel
