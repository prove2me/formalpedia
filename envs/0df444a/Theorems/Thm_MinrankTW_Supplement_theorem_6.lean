-- Prove2me | Theorems.Thm_MinrankTW_Supplement_theorem_6
-- name    : MinrankTW.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:08:02.832129+00:00
-- url     : https://prove2.me/theorems/5d05e7d6-20ca-443d-81ce-28a08819a781
-- title:
--   Theorem 6 — under SETH, no $q^{(1/4-\varepsilon)w^2}\mathrm{poly}(n)$ algorithm for fixed/free completion to rank $\le r$, even with a width-$w$ path decomposition
-- statement:
--   Assume SETH. For every fixed finite field $\mathbb F_q$ and every $0<\varepsilon<1/4$, no deterministic algorithm decides whether an $n\times n$ matrix whose entries are each fixed or unrestricted has a completion of rank at most a given $r$ in time
--   $$
--   q^{(1/4-\varepsilon)w^2}\,\mathrm{poly}(n),
--   $$
--   even when a width-$w$ path decomposition of its support graph is supplied.
--
--   Precisely: if SETH holds on the logarithmic-cost RAM, then for every finite field with a fixed encoding and every real $0<\varepsilon<1/4$ there are no program and constants $C,k$ such that, for all $n,N,w,r$ with $r\le n$, every $n\times n$ fixed/free matrix $A$ and every path decomposition of its support graph on $N$ nodes with bags of at most $w+1$ vertices, the program run on the encoding of $(A,\text{decomposition},r)$ halts within cost
--   $$
--   C\,q^{(1/4-\varepsilon)w^2}\,(n+N+1)^k
--   $$
--   and outputs $1$ in cell $0$ exactly when $A$ has a completion of rank at most $r$.
--
--   Together with Theorem 2, whose exponent is $\lfloor (w+1)^2/4\rfloor$, this shows that the constant $1/4$ in the exponent is optimal under SETH for fixed/free completion.
--
--   Differences from the source:
--   - reading: "over a fixed finite field F_q" (§1.2, p.4) → for every finite field F with an encoding e : F ≃ Fin q there exist a program P and constants C, k; reason: the field is fixed before the algorithm; the constants depend on q only
--   - reading: SETH: "for every δ > 0, some fixed clause width d rules out a 2^{(1−δ)N} poly(N) algorithm for d-SAT" → SETH on MinrankTW.RAM: for every real δ > 0 some d such that no program decides d-SAT within cost C·2^{(1−δ)N}·(L + 1)^k, L the length of the encoded formula; reason: the standard SETH; with poly(N) alone formulas with many repeated clauses would make the hypothesis trivially true and the theorem unconditional
--   - generalization: time q^{(1/4−ε)w²} poly(n) → cost ≤ C·q^{(1/4−ε)w²}·(n + N + 1)^k with N the size of the supplied decomposition; reason: a larger budget excludes more algorithms; specializes to poly(n)
--   - generalization: a given r → instances with r ≤ n; reason: an algorithm for all r is in particular one for r ≤ n, so excluding the latter is stronger; for r ≥ n the answer is always yes
--   - encoding: a width-w path decomposition is supplied → a bag table along the path 0 – ⋯ – (N − 1) forming an IsTreeDecomposition of supportGraph (fixedFree A) with SimpleGraph.pathGraph N, bags ≤ w + 1; reason: every path decomposition relabels to this order; width = max bag size − 1
--   - encoding: an n × n matrix whose entries are each fixed or unrestricted, deterministic algorithm, time → fixedFree A for a table A : Fin n → Fin n → Option F; the input layout thm6Input (the published thm2Input with m = n, plus r); total cost of MinrankTW.RAM bounded by the floor of the real bound; reason: same instances; cost is a natural number, so cost ≤ ⌊x⌋ iff cost ≤ x
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 6, p.20 (SETH p.19; reduction §B, p.19)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_MinrankTW_IsCompletion
import Definitions.Def_MinrankTW_supportGraph
import Definitions.Def_MinrankTW_RAM
import Definitions.Def_MinrankTW_Supplement_fixedFree
import Definitions.Def_MinrankTW_Supplement_SETH
import Definitions.Def_MinrankTW_Supplement_thm6Input

namespace MinrankTW.Supplement

/-- **Theorem 6** (Conditional lower bound), Perles–Weinstein, *Efficient Algorithms for Minrank and
Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991),
p.20. Assume SETH. For every fixed finite field `F_q` and every `0 < ε < 1/4`, no deterministic
algorithm decides whether an `n × n` matrix whose entries are each fixed or unrestricted has a
completion of rank at most a given `r` in time `q^{(1/4−ε)w²} poly(n)`, even when a width-`w` path
decomposition of its support graph is supplied.

**Formalization Note** `SETH` is the hypothesis of p.19 on the same machine `MinrankTW.RAM`. The
conclusion: for every finite field `F` with encoding `e` and every real `0 < ε < 1/4` there are no
program `P` and constants `C, k` such that for all `n, N, w, r` with `r ≤ n`, every fixed/free table
`A` and every bag table forming a path decomposition (along `0 – ⋯ – (N − 1)`) of the support graph
with bags of size at most `w + 1`, `P` run on `thm6Input` halts within cost
`C·q^{(1/4−ε)w²}·(n + N + 1)^k` with cell `0` equal to `1` exactly when some completion has rank at
most `r`. -/
theorem theorem_6 : SETH →
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (e : F ≃ Fin (Fintype.card F))
      (ε : ℝ), 0 < ε → ε < 1 / 4 →
      ¬ ∃ (P : List Instr) (C k : ℕ), ∀ (n N w r : ℕ) (A : Fin n → Fin n → Option F)
          (bag : Fin N → Fin n ⊕ Fin n → Bool),
          r ≤ n →
          RobertsonSeymour1986.GM5.IsTreeDecomposition (MinrankTW.supportGraph (fixedFree A))
            (SimpleGraph.pathGraph N) (fun s => Finset.univ.filter fun u => bag s u = true) →
          (∀ s, (Finset.univ.filter fun u => bag s u = true).card ≤ w + 1) →
          HaltsWithin P (thm6Input e n N r A bag)
            ⌊(C : ℝ) * (Fintype.card F : ℝ) ^ ((1 / 4 - ε) * (w : ℝ) ^ 2) *
              ((n : ℝ) + N + 1) ^ k⌋₊
            (fun out => out 0 = 1 ↔
              ∃ M : Matrix (Fin n) (Fin n) F, MinrankTW.IsCompletion (fixedFree A) M ∧
                M.rank ≤ r) := by sorry

end MinrankTW.Supplement
