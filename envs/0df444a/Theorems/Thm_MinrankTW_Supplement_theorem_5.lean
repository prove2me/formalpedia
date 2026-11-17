-- Prove2me | Theorems.Thm_MinrankTW_Supplement_theorem_5
-- name    : MinrankTW.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:07:24.523048+00:00
-- url     : https://prove2.me/theorems/d5fed9ff-738f-430b-a727-f69f5ed29290
-- title:
--   Theorem 5 — $T$ circuits on $v$ inputs as a square fixed/free matrix with a fixed $I_r$, $r=\lceil\sqrt v\rceil+4T$, and a path decomposition of width $\le 2\lceil\sqrt v\rceil+2g+4$
-- statement:
--   Let $T$ arithmetic circuits share $v\ge1$ inputs over $\mathbb F_q$. Each circuit has at most $g$ gates of the forms $c=ab$ and $c=\lambda a+\mu b+\nu$, with prescribed constants $\lambda,\mu,\nu\in\mathbb F_q$; arguments are inputs or earlier gates of that circuit, and designated outputs must equal one. Set $s=\lceil\sqrt v\rceil$. In polynomial time one can construct a square fixed/free matrix whose rank-$r$ completions correspond bijectively to satisfying input assignments, where
--   $$
--   r=s+4T,\qquad w\le 2s+2g+4. \tag{27}
--   $$
--   The matrix contains a fixed $I_r$, and a support path decomposition of width at most $w$ is supplied.
--
--   Precisely: for every finite field with a fixed encoding there are one logarithmic-cost RAM program and constants $C,k$ such that, for all $v\ge1$, $g$ and lists of $T$ well-formed circuits with at most $g$ gates each, the program halts at cost at most $C\,(L+v+1)^k$, where $L$ is the input length, and outputs
--
--   1. an $n\times n$ fixed/free matrix $A$;
--   2. $r$ distinct rows and $r$ distinct columns on which the fixed entries of $A$ form the identity $I_r$, $r=s+4T$;
--   3. a path decomposition of the support graph of $A$ with every bag of at most $2s+2g+5$ vertices;
--   4. $v$ positions of $A$ such that reading the entries at these positions is a bijection from the completions of $A$ of rank exactly $r$ onto the input assignments that satisfy every circuit.
--
--   Applied to Boolean formulas, the construction reduces bounded-clause-width SAT to fixed/free matrix completion with support width $O(\sqrt N)$, which is the basis of the conditional lower bound (Theorem 6).
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" (§1.2, p.4) → for every finite field F with an encoding e : F ≃ Fin q there exist a program P and constants C, k; reason: the field is fixed before the algorithm; the constants depend on q only
--   - encoding: T arithmetic circuits sharing v inputs, gates c = ab and c = λa + µb + ν with arguments inputs or earlier gates → a list cs of Circuit F v (T = cs.length), gates mul/affine with arguments Arg.input i or Arg.gate j, Circuit.WellFormed (gate arguments j < k), at most g gates each; reason: a direct transcription; zero coefficients still give constants and one-argument gates
--   - generalization: designated outputs → a list of arguments of the circuit, each an input or a gate (possibly empty, repetitions allowed); reason: covers the reading in which outputs are gates; the proof (p.19) tests an output o through its value row ρ_o, which inputs and gates both have, with no extra gate
--   - encoding: in polynomial time → total cost ≤ C·(L + v + 1)^k on MinrankTW.RAM, L the length of the input list circuitsInput; reason: polynomial in the size of the description of the circuits and the v inputs
--   - encoding: s = ⌈√v⌉ → ⌈Real.sqrt v⌉₊; reason: the same natural number
--   - reading: rank-r completions correspond bijectively to satisfying input assignments → the output lists v positions, and M ↦ (M at those positions) is a bijection (Set.BijOn) from the completions of rank exactly r onto the assignments satisfying every circuit; reason: the proof stores the inputs in free entries of V (p.18); an explicit bijection is the stronger reading of the correspondence
--   - encoding: the matrix contains a fixed I_r → injective row and column index maps rowI, colI with A(rowI a, colI b) fixed to 1 if a = b and 0 otherwise; reason: a fixed identity submatrix
--   - encoding: a support path decomposition of width at most w is supplied → the output bag table on the path 0 – ⋯ – (N − 1) is an IsTreeDecomposition of supportGraph (fixedFree A) along SimpleGraph.pathGraph N with every bag of at most 2s + 2g + 5 vertices; reason: a path decomposition is a tree decomposition whose tree is a path (p.5); width = max bag size − 1
--   - encoding: the constructed matrix and decomposition → the output layout thm5Output (n, N, r, entry codes, bag bits, identity indices, read-out positions); reason: a decodable layout of polynomial size
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 5, p.18, Eq. (27) (proof pp.18–19)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_IsCompletion
import Definitions.Def_MinrankTW_supportGraph
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_Supplement_fixedFree
import Definitions.Def_MinrankTW_Supplement_Circuit
import Definitions.Def_MinrankTW_Supplement_thm5Output

namespace MinrankTW.Supplement

/-- **Theorem 5** (Arithmetic circuits at small width), Perles–Weinstein, *Efficient Algorithms for
Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256
32a91384…c57991), p.18, Eq. (27). Let `T` arithmetic circuits share `v ≥ 1` inputs over `F_q`, each
with at most `g` gates of the forms `c = ab` and `c = λa + µb + ν`, arguments inputs or earlier
gates, designated outputs required to equal one. Put `s = ⌈√v⌉`. In polynomial time one can
construct a square fixed/free matrix whose rank-`r` completions correspond bijectively to satisfying
input assignments, where `r = s + 4T` and `w ≤ 2s + 2g + 4`; the matrix contains a fixed `I_r`, and
a support path decomposition of width at most `w` is supplied.

**Formalization Note** For every finite field `F` with encoding `e` there are one program `P` of
`MinrankTW.RAM` and constants `C, k` such that for all `v ≥ 1`, `g` and well-formed circuits
`cs` (`T = cs.length`) with at most `g` gates each, `P` run on `circuitsInput e v cs` halts at
cost at most `C·(L + v + 1)^k` (`L` the input length) with output, in the layout `thm5Output`, an
`n × n` fixed/free table `A`, a path decomposition on `N` nodes (path `0 – ⋯ – (N − 1)`) and
`r = s + 4T` such that:
1. rows `rowI` and columns `colI` (injective) carry fixed entries forming `I_r`;
2. the bags form a tree decomposition of the support graph of `A` along the path, each bag of size
   at most `2s + 2g + 5` (width `≤ 2s + 2g + 4`);
3. reading the `v` entries at the supplied positions `pos` is a bijection from the completions of
   `A` of rank exactly `r` onto the input assignments satisfying every circuit. -/
theorem theorem_5 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (e : F ≃ Fin (Fintype.card F)) :
    ∃ (P : List Instr) (C k : ℕ), ∀ (v g : ℕ) (cs : List (Circuit F v)),
      1 ≤ v → (∀ c ∈ cs, c.WellFormed ∧ c.gates.length ≤ g) →
      HaltsWithin P (fun i => (circuitsInput e v cs).getD i 0)
        (C * ((circuitsInput e v cs).length + v + 1) ^ k)
        (fun out => ∃ (n N : ℕ) (A : Fin n → Fin n → Option F)
          (bag : Fin N → Fin n ⊕ Fin n → Bool)
          (rowI colI : Fin (⌈Real.sqrt v⌉₊ + 4 * cs.length) → Fin n)
          (pos : Fin v → Fin n × Fin n),
          (∀ i < (thm5Output e n N (⌈Real.sqrt v⌉₊ + 4 * cs.length) v A bag rowI colI pos).length,
            out i = (thm5Output e n N (⌈Real.sqrt v⌉₊ + 4 * cs.length) v A bag rowI colI
              pos).getD i 0) ∧
          Function.Injective rowI ∧ Function.Injective colI ∧
          (∀ a b, A (rowI a) (colI b) = some (if a = b then 1 else 0)) ∧
          RobertsonSeymour1986.GM5.IsTreeDecomposition (MinrankTW.supportGraph (fixedFree A))
            (SimpleGraph.pathGraph N) (fun s => Finset.univ.filter fun u => bag s u = true) ∧
          (∀ s, (Finset.univ.filter fun u => bag s u = true).card ≤
            2 * ⌈Real.sqrt v⌉₊ + 2 * g + 4 + 1) ∧
          Set.BijOn (fun (M : Matrix (Fin n) (Fin n) F) (i : Fin v) => M (pos i).1 (pos i).2)
            {M | MinrankTW.IsCompletion (fixedFree A) M ∧
              M.rank = ⌈Real.sqrt v⌉₊ + 4 * cs.length}
            {x | ∀ c ∈ cs, c.Satisfied x}) := by sorry

end MinrankTW.Supplement
