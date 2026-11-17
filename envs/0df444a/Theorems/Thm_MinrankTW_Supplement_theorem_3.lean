-- Prove2me | Theorems.Thm_MinrankTW_Supplement_theorem_3
-- name    : MinrankTW.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:06:41.410351+00:00
-- url     : https://prove2.me/theorems/07701486-8d63-4341-9a30-9f3e4a13d707
-- title:
--   Theorem 3 — minrank and an optimal fitting matrix in $q^{(w+1)^2}\mathrm{poly}(n)$ time from a width-$w$ decomposition of the complement
-- statement:
--   Given an $n$-vertex graph $G$ and a width-$w$ tree decomposition of the complement $\overline G$ of polynomial size, one can compute $\mathrm{minrank}_{\mathbb F_q}(G)$ and an optimal fitting matrix in deterministic time
--   $$
--   q^{(w+1)^2}\,\mathrm{poly}(n).
--   $$
--
--   Precisely: for every finite field $\mathbb F_q$ with a fixed encoding of its elements there are one logarithmic-cost RAM program and constants $C,k$, depending only on the field and its encoding, such that for all $n,N,w$, every graph $G$ on $n$ vertices and every tree decomposition of $\overline G$ on $N$ nodes with bags of at most $w+1$ vertices, the program run on the input layout of Theorem 1 halts at total cost at most
--   $$
--   C\,q^{(w+1)^2}\,(n+N+1)^k
--   $$
--   and outputs $\mathrm{minrank}_{\mathbb F_q}(G)$ in cell $0$ and, in cells $1,\dots,n^2$, the entry codes (row by row) of a normalized fitting matrix of $G$ of rank $\mathrm{minrank}_{\mathbb F_q}(G)$.
--
--   The bound holds when the complement has small treewidth, even if $G$ itself has large treewidth, so it complements Theorem 1.
--
--   **Formalization Note** The complement is `(fromRel edge)ᶜ`: distinct vertices are adjacent in $\overline G$ exactly when they are not adjacent in $G$.
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" (§1.2, p.4) → for every finite field F with an encoding e : F ≃ Fin q there exist a program P and constants C, k; reason: the field is fixed before the algorithm; the constants depend on q only
--   - generalization: a tree decomposition "of polynomial size" → any number N of nodes, with N inside the polynomial (n + N + 1)^k; reason: specializes to every polynomial bound N ≤ poly(n)
--   - encoding: width w → every bag has at most w + 1 vertices; reason: width = max |B_t| − 1 (p.4)
--   - encoding: deterministic time → total cost of a program of the published logarithmic-cost RAM MinrankTW.RAM; reason: the source counts polynomial bit cost (p.17); same machine as the goal
--   - encoding: the input graph G and the decomposition of Ḡ → Boolean tables in the published layout thm1Input; the decomposition hypothesis is IsTreeDecomposition of (fromRel edge)ᶜ; reason: every graph and decomposition has such an encoding of polynomial size; the overline lost in the text layer was checked on the rendered p.4
--   - generalization: an optimal fitting matrix → a normalized fitting matrix of rank minrank, as entry codes in cells 1..n²; reason: a normalized fitting matrix fits G; the proof's witness satisfies a_i b_i = 1, Eq. (29)
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 3, p.4 (proof §C.2, pp.21–22)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_IsNormalizedFit
import Definitions.Def_MinrankTW_minrank
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_thm1Input

namespace MinrankTW.Supplement

/-- **Theorem 3** (Minrank from a decomposition of the complement), Perles–Weinstein, *Efficient
Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript
(sha256 32a91384…c57991), p.4 (proof §C.2, pp.21–22). Given an `n`-vertex graph `G` and a width-`w`
tree decomposition of the complement `Ḡ` of polynomial size, one can compute `minrank_{F_q}(G)` and
an optimal fitting matrix in deterministic time `q^{(w+1)²} poly(n)`.

**Formalization Note** As in the published goal `MinrankTW.theorem_1`: for every finite field `F`
with encoding `e : F ≃ Fin q` there are one program `P` of the logarithmic-cost RAM
`MinrankTW.RAM` and constants `C, k` such that for all `n, N, w`, every graph table `edge` and every
tree table `tree` on `N` nodes with bag table `bag` forming a tree decomposition (the published
`IsTreeDecomposition`) of the **complement** `(fromRel edge)ᶜ` with every bag of size at most
`w + 1`, the run of `P` on the layout `thm1Input` halts at total cost at most
`C · q^{(w+1)²} · (n + N + 1)^k` with cell `0` holding `minrank_F(G)` and cells `1, …, n²` the codes
`e(M_ij)` (row by row) of a normalized fitting matrix `M` of `G` of rank `minrank_F(G)`. -/
theorem theorem_3 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    ∃ (P : List Instr) (C k : ℕ), ∀ (n N w : ℕ) (edge : Fin n → Fin n → Bool)
      (tree : Fin N → Fin N → Bool) (bag : Fin N → Fin n → Bool),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (SimpleGraph.fromRel fun u v => edge u v = true)ᶜ
        (SimpleGraph.fromRel fun s s' => tree s s' = true)
        (fun s => Finset.univ.filter fun v => bag s v = true) →
      (∀ s, (Finset.univ.filter fun v => bag s v = true).card ≤ w + 1) →
      HaltsWithin P (thm1Input n N edge tree bag)
        (C * Fintype.card F ^ ((w + 1) ^ 2) * (n + N + 1) ^ k)
        (fun out =>
          out 0 = minrank F (SimpleGraph.fromRel fun u v => edge u v = true) ∧
          ∃ M : Matrix (Fin n) (Fin n) F,
            IsNormalizedFit (SimpleGraph.fromRel fun u v => edge u v = true) M ∧
            M.rank = out 0 ∧
            ∀ i j : Fin n, out (1 + ((i : ℕ) * n + j)) = (e (M i j) : ℕ)) := by sorry

end MinrankTW.Supplement
