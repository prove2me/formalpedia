-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_dac_shared_properties
-- name    : MSTCuts2027.Parallel.dac_shared_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:42.893924+00:00
-- url     : https://prove2.me/theorems/27f5a6f4-a205-4885-b5ce-7cdaec574710
-- title:
--   Lemma 14 — the five parallel properties of DACPruneEdges and DACAssignMincut
-- statement:
--   There is a constant $c$ such that for every symmetric real cut function $F$, every block $B$ of vertices listed at position $l$, and every $x\notin B$, both DACPruneEdges and DACAssignMincut on the recursion tree $T(x)$ satisfy:
--
--   1. **Constant cost per node.** An internal node costs work and depth at most $c$.
--   2. **Independence within a level.** Two distinct nodes of one level, run from the same memory, are independent: neither writes a location the other reads or writes.
--   3. **Dependence on the adjacent level only.** A node of DACPruneEdges reads, of the tree, only the entries of its children, and its own output cell, and it writes only that output cell. A node of DACAssignMincut reads, of the tree, only itself and its two children, and of $M$ and the values only the entries of $(x,w)$ and $(w,e)$, where $w$ is the edge it stores and $e$ the pruned vertex; it writes only the entries of $(x,e)$ and $(e,x)$. Here $(w,e)$ lies inside $B$, and $(x,w)$ is the pointer of the edge stored at the node, known from the level above.
--   4. **Total cost.** Each routine has work at most $c|B|$ and depth at most $c(\lceil\log_2|B|\rceil+1)$, and DACPruneEdges has exactly $\lceil\log_2|B|\rceil$ rounds.
--   5. **Independence between trees.** For $x'\ne x$ outside $B$, the computation of $T(x)$ and that of $T(x')$, run from the same memory, are independent.
--
--   Levels are executed bottom-up in DACPruneEdges and top-down in DACAssignMincut. Items 1 to 3 for DACPruneEdges hold on any memory in which the rounds up to the node's level are complete.
--
--   Differences from the source:
--   - encoding: O(·) time bound → explicit constant c fixed before the instance, bounding the work (and depth where stated) of a machine run; reason: the paper gives no numerical constant; c may depend only on the fixed program
--   - encoding: any set of vertices → a duplicate-free list L in the array ord at positions l, …; reason: every finite set has such a listing, so no instance is lost; the list gives the machine random access to the set
--   - reading: level i depends only on level i − 1 → explicit bounds on the reads and writes of a node, in the execution direction of each routine; the node of DACPruneEdges may also read back the output cell it just wrote; reason: for DACAssignMincut the pointer M(x, w) of the edge a node stores may have been written higher than the adjacent level when w survived several levels, so the literal claim about writes is read as: the node uses the record of the edge stored at it, which is known once the level above is done
--   - encoding: can be performed independently → the machine outcomes are Compatible: no location written by one thread is read or written by the other; reason: this is the condition under which the machine runs threads concurrently
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 14, printed p. 22–23, PDF p. 24–25

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms

namespace MSTCuts2027.Parallel

/-- Lemma 14: the five shared properties of `DACPruneEdges` and `DACAssignMincut` on the recursion
tree `T(x)`, for the machine's actual footprints. "Independent" means `Compatible`. The first part is
`DACPruneEdges`, on any memory `τ` where the rounds up to `j` are done; the second part is
`DACAssignMincut`, on any memory `τ` holding the complete tree. -/
theorem dac_shared_properties :
    ∃ c : ℕ, ∀ (n : ℕ) (F : Finset (Fin n) → ℝ), IsSymmetricCutFunction F →
      ∀ (P : Oracle ℝ n) (l : ℕ) (L : List (Fin n)) (x : Fin n),
        L ≠ [] → L.Nodup → l + L.length ≤ n → x ∉ L →
        -- `DACPruneEdges`
        (∀ τ : Store ℝ, IsReady n τ → TableOK F τ L.toFinset →
          -- properties 1 and 3: a node of round `j` costs `O(1)` and uses only round `j` of `T(x)`
          (∀ j i, j < Nat.clog 2 L.length → 2 * i + 1 < roundSize L.length j →
            TreeUpTo τ.mem x l L j →
            ∃ (u v : Fin n) (p : ℕ) (o : Outcome ℝ),
              τ.mem (treeAddr n x l j (2 * i)) = ((u : ℕ) : ℤ) ∧
              τ.mem (treeAddr n x l j (2 * i + 1)) = ((v : ℕ) : ℤ) ∧
              τ.mem (tableAddr n u v) = (p : ℤ) ∧
              Halts (machine P) algorithms Prog.pPruneNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i : ℤ)] τ o ∧
              o.work ≤ c ∧ o.depth ≤ c ∧
              o.reads ⊆ pruneNodeReads n x l j i u v p ∧
              o.writes = {Loc.word (treeAddr n x l (j + 1) i)}) ∧
          -- property 2: nodes of one round are independent
          (∀ j i i', j < Nat.clog 2 L.length → 2 * i + 1 < roundSize L.length j →
            2 * i' + 1 < roundSize L.length j → i ≠ i' → TreeUpTo τ.mem x l L j →
            ∀ o o' : Outcome ℝ,
              Halts (machine P) algorithms Prog.pPruneNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i : ℤ)] τ o →
              Halts (machine P) algorithms Prog.pPruneNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i' : ℤ)] τ o' →
              Compatible o o') ∧
          -- properties 4 and 5, given the vertex array
          (OrdOK τ l L →
            (∃ o : Outcome ℝ,
              Halts (machine P) algorithms Prog.pPruneOne
                [((x : ℕ) : ℤ), (l : ℤ), (L.length : ℤ)] τ o ∧
              o.work ≤ c * L.length ∧ o.depth ≤ c * (Nat.clog 2 L.length + 1) ∧
              o.store.mem (roundsAddr n x l) = (Nat.clog 2 L.length : ℤ)) ∧
            ∀ (x' : Fin n), x' ∉ L → x' ≠ x → ∀ o o' : Outcome ℝ,
              Halts (machine P) algorithms Prog.pPruneOne
                [((x : ℕ) : ℤ), (l : ℤ), (L.length : ℤ)] τ o →
              Halts (machine P) algorithms Prog.pPruneOne
                [((x' : ℕ) : ℤ), (l : ℤ), (L.length : ℤ)] τ o' →
              Compatible o o')) ∧
        -- `DACAssignMincut`
        (∀ τ : Store ℝ, IsReady n τ → IsRecursionTree τ.mem x l L →
          -- properties 1 and 3: a node costs `O(1)`, and uses only itself, its children and the
          -- pointer of the edge it stores, which the level above determined
          (∀ j i, j < Nat.clog 2 L.length → 2 * i + 1 < roundSize L.length j →
            ∃ (w e : Fin n) (o : Outcome ℝ),
              τ.mem (treeAddr n x l (j + 1) i) = ((w : ℕ) : ℤ) ∧
              ((τ.mem (treeAddr n x l j (2 * i)) = ((w : ℕ) : ℤ) ∧
                  τ.mem (treeAddr n x l j (2 * i + 1)) = ((e : ℕ) : ℤ)) ∨
               (τ.mem (treeAddr n x l j (2 * i)) = ((e : ℕ) : ℤ) ∧
                  τ.mem (treeAddr n x l j (2 * i + 1)) = ((w : ℕ) : ℤ))) ∧
              Halts (machine P) algorithms Prog.pAssignNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i : ℤ)] τ o ∧
              o.work ≤ c ∧ o.depth ≤ c ∧
              o.reads ⊆ assignNodeReads n x l j i w e ∧
              o.writes = assignNodeWrites n x e) ∧
          -- property 2: nodes of one round are independent
          (∀ j i i', j < Nat.clog 2 L.length → 2 * i + 1 < roundSize L.length j →
            2 * i' + 1 < roundSize L.length j → i ≠ i' →
            ∀ o o' : Outcome ℝ,
              Halts (machine P) algorithms Prog.pAssignNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i : ℤ)] τ o →
              Halts (machine P) algorithms Prog.pAssignNode
                [((x : ℕ) : ℤ), (l : ℤ), (j : ℤ), (i' : ℤ)] τ o' →
              Compatible o o') ∧
          -- property 4
          (∃ o : Outcome ℝ,
            Halts (machine P) algorithms Prog.pAssignLoop
              [((x : ℕ) : ℤ), (l : ℤ), 0, (L.length : ℤ)] τ o ∧
            o.work ≤ c * L.length ∧ o.depth ≤ c * (Nat.clog 2 L.length + 1)) ∧
          -- property 5
          (∀ (x' : Fin n), x' ∉ L → x' ≠ x → IsRecursionTree τ.mem x' l L →
            ∀ o o' : Outcome ℝ,
              Halts (machine P) algorithms Prog.pAssignLoop
                [((x : ℕ) : ℤ), (l : ℤ), 0, (L.length : ℤ)] τ o →
              Halts (machine P) algorithms Prog.pAssignLoop
                [((x' : ℕ) : ℤ), (l : ℤ), 0, (L.length : ℤ)] τ o' →
              Compatible o o')) := by sorry

end MSTCuts2027.Parallel
