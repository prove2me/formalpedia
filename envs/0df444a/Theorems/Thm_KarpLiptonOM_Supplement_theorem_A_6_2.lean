-- Prove2me | Theorems.Thm_KarpLiptonOM_Supplement_theorem_A_6_2
-- name    : KarpLiptonOM.Supplement.theorem_A_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:44:26.68483+00:00
-- url     : https://prove2.me/theorems/345f583c-7f0f-4409-a268-8aba64d27aa5
-- title:
--   Theorem A.6.2 — $\mathrm{ONP}\subseteq\mathrm{OGTD}[\mathrm{prSBP}]$
-- statement:
--   Every language with oblivious NP witnesses has polynomial-size advice that can be computed from $1^n$ by a polynomial-time machine with an approximate-counting oracle and decoded in polynomial time:
--
--   $$
--   \mathrm{ONP}\subseteq\mathrm{OGTD}[\mathrm{prSBP}] .
--   $$
--
--   Here $L\in\mathrm{ONP}$ if a polynomial-time verifier $V$ and strings $w_n$ of polynomial length satisfy, for every $x\in\{0,1\}^n$, $x\in L\Rightarrow V(x,w_n)=1$ and $x\notin L\Rightarrow V(x,w)=0$ for all $w$; and $\mathrm{OGTD}[\mathrm{prSBP}]=\mathrm{OGTD}[\mathrm{SSE}]$ is the class of languages $L$ for which a deterministic polynomial-time oracle machine $G$ outputs on $1^n$, with every oracle consistent with SSE, an advice string of a fixed polynomial length from which a polynomial-time decoder $D$ computes $L(x)$ for every $x\in\{0,1\}^n$.
--
--   So oblivious witnesses can be replaced by a short list of witnesses found with approximate counting; the same construction, applied twice, gives Theorem A.6.3.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 not imposed), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention of the published base definitions; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: prSBP oracle; SSE with yes-instances (C, m), #C ≥ m, and no-instances (C, m), #C ≤ m/2, m ≥ 1 in binary (p.22) → the oracle is SSE (P^prSBP = PC {SSE}, FP^prSBP = InFP SSE, OGTD[prSBP] = OGTD {SSE} Set.univ); instances are strings sseInst n s C m = 1ⁿ0 1ˢ0 code(C) bin(m) for a circuit C with n inputs and at most s gates; #C ≤ m/2 as 2·#C ≤ m; the no-set asks 2·#C ≤ m of every instance the string encodes; malformed strings and m = 0 are in neither set; reason: the paper's own identification of prSBP with its complete problem SSE (pp.22, 25); sseInst is injective on instances, so the no-set is the paper's, and every polynomial-time encoding of (C, m) gives the same classes
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.6.2, p.34

import Mathlib
import Definitions.Def_KarpLiptonOM_ONP
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_Supplement_SSE

namespace KarpLiptonOM.Supplement

/-- Theorem A.6.2 (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.34): `ONP ⊆ OGTD[prSBP]`. Every language with oblivious NP witnesses has
polynomial-size advice computable from `1ⁿ` in polynomial time with an oracle for approximate
counting, and decoded in polynomial time.

**Formalization Note** Strings, machines and classes are those of the published `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle (Definition A.2.1), lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. prSBP enters only through its complete problem SSE, as in the paper: `P^prSBP = PC {SSE}`, `FP^prSBP = InFP SSE`, `OGTD[prSBP] = OGTD {SSE} Set.univ` (pp.22, 25). The item's natural-language statement lists every difference from the page.

`OGTD[prSBP] = OGTD[SSE] = OGTD[FP^SSE, ∗, P]` is `OGTD {SSE} Set.univ` (no tester). -/
theorem theorem_A_6_2 : ONP ⊆ OGTD {SSE} Set.univ := by sorry

end KarpLiptonOM.Supplement
