-- Prove2me | Theorems.Thm_MinrankTW_theorem_1
-- name    : MinrankTW.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:52.812209+00:00
-- url     : https://prove2.me/theorems/082a0f3f-a450-4368-b5c1-b0b401c2e15b
-- title:
--   Theorem 1 — minrank, an optimal fitting matrix and all normalized rank counts in $q^{(w+1)^2}\mathrm{poly}(n)$ time
-- statement:
--   Given an $n$-vertex graph $G$ and a width-$w$ tree decomposition of $G$ of polynomial size, one can compute $\mathrm{minrank}_{\mathbb F_q}(G)$, an optimal fitting matrix, and the number of normalized fitting matrices of every rank in deterministic time
--   $$
--   q^{(w+1)^2}\,\mathrm{poly}(n).
--   $$
--
--   Precisely: for every finite field $\mathbb F_q$ with a fixed encoding of its elements there are one logarithmic-cost RAM program and constants $C,k$, depending only on the field and its encoding, such that for all $n,N,w$, every graph $G$ on $n$ vertices and every tree decomposition of $G$ on $N$ nodes with bags of at most $w+1$ vertices, the program run on the input layout halts at total cost at most
--   $$
--   C\,q^{(w+1)^2}\,(n+N+1)^k
--   $$
--   and outputs
--
--   1. $\mathrm{minrank}_{\mathbb F_q}(G)$;
--   2. a normalized fitting matrix of $G$ of rank $\mathrm{minrank}_{\mathbb F_q}(G)$ (its entry codes, row by row);
--   3. for every $j\le n$, the number of normalized fitting matrices of $G$ of rank $j$.
--
--   For graphs of polylogarithmic treewidth this is the first quasipolynomial-time algorithm for minrank, equivalently for the minimum length of a scalar linear index code.
--
--   **Formalization Note** The tree decomposition is the published `RobertsonSeymour1986.GM5.IsTreeDecomposition`.
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" → for every F and encoding e there exist P, C, k; reason: the field is fixed before the algorithm; constants depend on q only
--   - generalization: a tree decomposition "of polynomial size" → any number N of nodes, with N inside the polynomial (n + N + 1)^k; reason: specializes to every polynomial bound N ≤ poly(n)
--   - encoding: width w → every bag has at most w + 1 vertices; reason: width = max |B_t| − 1
--   - encoding: deterministic time → total cost of a logarithmic-cost RAM program; reason: the source counts polynomial bit cost (p.17)
--   - encoding: the input graph and decomposition → Boolean tables in the layout thm1Input; graph and tree read as fromRel of their tables, bags as the true entries of the bag table; reason: every graph and decomposition has such an encoding, of polynomial size
--   - generalization: an optimal fitting matrix → a normalized fitting matrix of rank minrank; reason: a normalized fitting matrix fits G; the source's witness is normalized (p.15)
--   - encoding: the number of normalized fitting matrices of every rank → the counts for every j ≤ n; reason: no n × n matrix has rank > n
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 1, p.3

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_IsNormalizedFit
import Definitions.Def_MinrankTW_minrank
import Definitions.Def_MinrankTW_fitCount
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_thm1Input

namespace MinrankTW

/-- **Theorem 1** (Faster Minrank for Low-Treewidth Graphs), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.3. Given an `n`-vertex
graph `G` and a width-`w` tree decomposition of `G` of polynomial size, one can compute
`minrank_{F_q}(G)`, an optimal fitting matrix, and the number of normalized fitting matrices of
every rank in deterministic time `q^{(w+1)²} poly(n)`.

**Formalization Note** For every finite field `F` (with `q = |F|` and a fixed encoding
`e : F ≃ Fin q`) there are one logarithmic-cost RAM program `P` and constants `C, k`,
depending only on `F` and `e`, such that for all `n, N, w`, every graph table `edge` on `n`
vertices and every tree table `tree` on `N` nodes with bag table `bag` forming a tree
decomposition (the published `IsTreeDecomposition`) of `G = fromRel edge` with all bags of size
at most `w + 1`, the run of `P` on `thm1Input` halts at total logarithmic cost at most
`C · q^{(w+1)²} · (n + N + 1)^k` with:
1. cell `0` holding `minrank_F(G)`;
2. cells `1, …, n²` holding the codes `e(M_ij)` (row by row) of a normalized fitting matrix `M`
   of rank `minrank_F(G)` (an optimal fitting matrix);
3. cell `1 + n² + j` holding the number of normalized fitting matrices of rank `j`, for every
   `j ≤ n` (larger ranks have none).
The decomposition size `N` is inside the polynomial ("of polynomial size"). -/
theorem theorem_1 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    ∃ (P : List Instr) (C k : ℕ), ∀ (n N w : ℕ) (edge : Fin n → Fin n → Bool)
      (tree : Fin N → Fin N → Bool) (bag : Fin N → Fin n → Bool),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (SimpleGraph.fromRel fun u v => edge u v = true)
        (SimpleGraph.fromRel fun s s' => tree s s' = true)
        (fun s => Finset.univ.filter fun v => bag s v = true) →
      (∀ s, (Finset.univ.filter fun v => bag s v = true).card ≤ w + 1) →
      HaltsWithin P (thm1Input n N edge tree bag)
        (C * Fintype.card F ^ ((w + 1) ^ 2) * (n + N + 1) ^ k)
        (fun out =>
          out 0 = minrank F (SimpleGraph.fromRel fun u v => edge u v = true) ∧
          (∃ M : Matrix (Fin n) (Fin n) F,
            IsNormalizedFit (SimpleGraph.fromRel fun u v => edge u v = true) M ∧
            M.rank = out 0 ∧
            ∀ i j : Fin n, out (1 + ((i : ℕ) * n + j)) = (e (M i j) : ℕ)) ∧
          ∀ j : ℕ, j ≤ n →
            out (1 + n * n + j) = fitCount F (SimpleGraph.fromRel fun u v => edge u v = true) j) := by sorry

end MinrankTW
