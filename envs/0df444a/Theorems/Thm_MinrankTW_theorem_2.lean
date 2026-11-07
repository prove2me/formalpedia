-- Prove2me | Theorems.Thm_MinrankTW_theorem_2
-- name    : MinrankTW.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:06.611616+00:00
-- url     : https://prove2.me/theorems/534b2640-3093-4e60-82fb-0af8b60e72f7
-- title:
--   Theorem 2 — a minimum-rank completion and all rank counts in $q^{\lfloor (w+1)^2/4\rfloor}\mathrm{poly}(m+n)$ time
-- statement:
--   Given independent entry constraints on an $m\times n$ matrix over $\mathbb F_q$ (every allowed set $S_{ij}$ nonempty) and a width-$w$ tree decomposition of their bipartite support graph of polynomial size, one can compute a minimum-rank completion and the number of completions of every rank in deterministic time
--   $$
--   q^{\lfloor (w+1)^2/4\rfloor}\,\mathrm{poly}(m+n).
--   $$
--
--   Precisely: for every finite field $\mathbb F_q$ with a fixed encoding of its elements there are one logarithmic-cost RAM program and constants $C,k$, depending only on the field and its encoding, such that for all $m,n,N,w$, all constraints $S$ with nonempty allowed sets, and every tree decomposition of the support graph on $N$ nodes with bags of at most $w+1$ vertices, the program run on the input layout halts at total cost at most $C\,q^{\lfloor (w+1)^2/4\rfloor}(m+n+N+1)^k$ and outputs
--
--   1. the minimum rank $r$ of a completion;
--   2. a completion of rank $r$ (its entry codes, row by row);
--   3. for every $j\le\min(m,n)$, the number of completions of rank $j$.
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" → for every F and encoding e there exist P, C, k; reason: the field is fixed before the algorithm; constants depend on q only
--   - generalization: a tree decomposition "of polynomial size" → any number N of nodes, with N inside the polynomial (m + n + N + 1)^k; reason: specializes to every polynomial bound N ≤ poly(m + n)
--   - encoding: width w → every bag has at most w + 1 vertices; reason: width = max |B_t| − 1
--   - encoding: deterministic time → total cost of a logarithmic-cost RAM program; reason: the source counts polynomial bit cost (p.17)
--   - encoding: the input (support edges and allowed sets, the decomposition) → the dense layout thm2Input: allowed sets as bitmasks, tree and bag tables, tree read as fromRel of its table; reason: standard encoding of polynomial size
--   - encoding: a minimum-rank completion → the minimum rank in cell 0, the codes of a completion of that rank, and minimality over all completions; reason: the output and its specification
--   - encoding: the number of completions of every rank → the counts for every j ≤ min(m, n); reason: no completion has larger rank
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 2, p.3

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_IsCompletion
import Definitions.Def_MinrankTW_supportGraph
import Definitions.Def_MinrankTW_completionCount
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_thm2Input

namespace MinrankTW

/-- **Theorem 2** (Independent entry constraints), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.3. Given independent entry
constraints on an `m × n` matrix and a width-`w` tree decomposition of its support graph of
polynomial size, one can compute a minimum-rank completion and the number of completions of every
rank in deterministic time `q^{⌊(w+1)²/4⌋} poly(m + n)`.

**Formalization Note** For every finite field `F` with its encoding `e : F ≃ Fin q` there are one
logarithmic-cost RAM program `P` and constants `C, k` (depending only on `F`, `e`) such that for
all `m, n, N, w`, all constraints `S` with nonempty allowed sets, and all tree tables on `N` nodes
with bag tables over the support vertices forming a tree decomposition of the support graph with
bags of size at most `w + 1`: run on the input layout `thm2Input`, `P` halts at total cost
`≤ C q^{⌊(w+1)²/4⌋} (m + n + N + 1)^k` with cell `0` holding the minimum completion rank `r`,
cells `1, …, mn` the codes (row by row) of a completion of rank `r`, and cell `1 + mn + j` the
number of rank-`j` completions for every `j ≤ min(m, n)` (larger ranks have none). The
decomposition size `N` is inside the polynomial. -/
theorem theorem_2 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    ∃ (P : List Instr) (C k : ℕ), ∀ (m n N w : ℕ) (S : Fin m → Fin n → Finset F)
      (tree : Fin N → Fin N → Bool) (bag : Fin N → Fin m ⊕ Fin n → Bool),
      (∀ i j, (S i j).Nonempty) →
      RobertsonSeymour1986.GM5.IsTreeDecomposition (supportGraph S)
        (SimpleGraph.fromRel fun s s' => tree s s' = true)
        (fun s => Finset.univ.filter fun u => bag s u = true) →
      (∀ s, (Finset.univ.filter fun u => bag s u = true).card ≤ w + 1) →
      HaltsWithin P (thm2Input e m n N S tree bag)
        (C * Fintype.card F ^ ((w + 1) ^ 2 / 4) * (m + n + N + 1) ^ k)
        (fun out =>
          (∃ M : Matrix (Fin m) (Fin n) F, IsCompletion S M ∧ M.rank = out 0 ∧
            ∀ (i : Fin m) (j : Fin n), out (1 + ((i : ℕ) * n + j)) = (e (M i j) : ℕ)) ∧
          (∀ M : Matrix (Fin m) (Fin n) F, IsCompletion S M → out 0 ≤ M.rank) ∧
          ∀ j : ℕ, j ≤ min m n → out (1 + m * n + j) = completionCount S j) := by sorry

end MinrankTW
