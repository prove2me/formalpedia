-- Prove2me | Theorems.Thm_KarpLiptonOM_Supplement_theorem_A_6_3
-- name    : KarpLiptonOM.Supplement.theorem_A_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:45:16.346223+00:00
-- url     : https://prove2.me/theorems/d6639b4d-d06c-48aa-8f2c-6ee6ae515864
-- title:
--   Theorem A.6.3 (= Theorem 4(3)) — $\mathrm O^{\mathrm P}_2\subseteq\mathrm{OGTD}[\mathrm{prSBP}]$
-- statement:
--   Every language in oblivious symmetric alternation has polynomial-size circuits that can be constructed from $1^n$ in polynomial time with an approximate-counting oracle:
--
--   $$
--   \mathrm O^{\mathrm P}_2\subseteq\mathrm{OGTD}[\mathrm{prSBP}] .
--   $$
--
--   Here $L\in\mathrm O^{\mathrm P}_2$ if there are a polynomial-time $V$ and polynomials $a,b$ such that $x\in L\Rightarrow\exists y\,\forall z\,V(x,y,z)=1$ and $x\notin L\Rightarrow\exists z\,\forall y\,V(x,y,z)=0$, with certificates $y_n$, $z_n$ that are irrefutable for all yes-inputs, respectively all no-inputs, of length $n$; and $\mathrm{OGTD}[\mathrm{prSBP}]=\mathrm{OGTD}[\mathrm{SSE}]$ is the class of languages whose advice for length $n$ is computed from $1^n$ by one deterministic polynomial-time machine, with every oracle consistent with SSE, and decoded in polynomial time.
--
--   This is part (3) of the paper's Theorem 4. It completes the oblivious chain $\mathrm{OGTD}[\mathrm{prMA}]\subseteq\mathrm{OL}^{\mathrm P}_2\subseteq\mathrm O^{\mathrm P}_2\subseteq\mathrm{OGTD}[\mathrm{prSBP}]$, the input-oblivious counterpart of $\mathrm P^{\mathrm{prMA}}\subseteq\mathrm L^{\mathrm P}_2\subseteq\mathrm S^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}}$. It is not a formal consequence of Theorem A.5.4, since $\mathrm O^{\mathrm P}_2\subseteq\mathrm{OGTD}[\mathrm{prS}^{\mathrm P}_2]$ is not known.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 not imposed), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention of the published base definitions; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: prSBP oracle; SSE with yes-instances (C, m), #C ≥ m, and no-instances (C, m), #C ≤ m/2, m ≥ 1 in binary (p.22) → the oracle is SSE (P^prSBP = PC {SSE}, FP^prSBP = InFP SSE, OGTD[prSBP] = OGTD {SSE} Set.univ); instances are strings sseInst n s C m = 1ⁿ0 1ˢ0 code(C) bin(m) for a circuit C with n inputs and at most s gates; #C ≤ m/2 as 2·#C ≤ m; the no-set asks 2·#C ≤ m of every instance the string encodes; malformed strings and m = 0 are in neither set; reason: the paper's own identification of prSBP with its complete problem SSE (pp.22, 25); sseInst is injective on instances, so the no-set is the paper's, and every polynomial-time encoding of (C, m) gives the same classes
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.6.3 (part (3) of Theorem 4), p.34; Theorem 4(3), p.6

import Mathlib
import Definitions.Def_KarpLiptonOM_OP2
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_Supplement_SSE

namespace KarpLiptonOM.Supplement

/-- Theorem A.6.3 (part (3) of Theorem 4; Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.34, and p.6): `O₂^P ⊆ OGTD[prSBP]`; that is, every
language in `O₂^P` has polynomial-size circuits constructible in `FP^prSBP`.

**Formalization Note** Strings, machines and classes are those of the published `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle (Definition A.2.1), lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. prSBP enters only through its complete problem SSE, as in the paper: `P^prSBP = PC {SSE}`, `FP^prSBP = InFP SSE`, `OGTD[prSBP] = OGTD {SSE} Set.univ` (pp.22, 25). The item's natural-language statement lists every difference from the page.

`OGTD[prSBP] = OGTD[SSE] = OGTD[FP^SSE, ∗, P]` is `OGTD {SSE} Set.univ` (no tester); `O₂^P` is the
published language class `KarpLiptonOM.OP2`. -/
theorem theorem_A_6_3 : OP2 ⊆ OGTD {SSE} Set.univ := by sorry

end KarpLiptonOM.Supplement
