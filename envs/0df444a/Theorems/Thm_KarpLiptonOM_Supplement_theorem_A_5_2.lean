-- Prove2me | Theorems.Thm_KarpLiptonOM_Supplement_theorem_A_5_2
-- name    : KarpLiptonOM.Supplement.theorem_A_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:42:58.873977+00:00
-- url     : https://prove2.me/theorems/8d0b2fa3-b3ff-4bc0-9723-f4686ebc9bc2
-- title:
--   Theorem A.5.2 (= Theorem 5.2) — Goldreich–Wigderson lemma with approximate counting: a certificate with $\le 3(a+b)+1$ elements in $\mathrm{FP}^{\mathrm{SSE}}$
-- statement:
--   Let $V:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ be a circuit, read as a Boolean matrix in which row $y$ beats column $z$ if $V(y,z)=1$ and column $z$ beats row $y$ if $V(y,z)=0$. There is one deterministic polynomial-time oracle machine which, for **every** language $O$ consistent with the approximate-counting problem SSE, on input $V$ outputs either
--
--   1. a **row-side** collectively irrefutable certificate: a set $R\subseteq\{0,1\}^a$ such that every column is beaten by some row of $R$, or
--   2. a **column-side** collectively irrefutable certificate: a set $T\subseteq\{0,1\}^b$ such that every row is beaten by some column of $T$,
--
--   with at most
--
--   $$
--   3(a+b)+1
--   $$
--
--   elements, and the output says which side it is. If $V$ has an irrefutable row (a row beating every column), the output is row-side.
--
--   In short, a succinctly given matrix always has a short collectively irrefutable certificate on one side, and one can be found in $\mathrm{FP}^{\mathrm{prSBP}}$; Chakaravarthy and Roy found one with a $\mathrm{prAM}$ oracle. The lemma yields $\mathrm{S}^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}}$ (Theorem A.5.4), the minimum-finding behind $\mathrm L^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}}$, and the advice of Theorems A.6.2 and A.6.3.
--
--   **Formalization Note** The machine's input is $1^a0\,1^b0\,\langle V\rangle$ (`gwInput`) for a circuit with at most $s$ gates; its output is a side bit followed by the certificate's elements concatenated.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 not imposed), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention of the published base definitions; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: prSBP oracle; SSE with yes-instances (C, m), #C ≥ m, and no-instances (C, m), #C ≤ m/2, m ≥ 1 in binary (p.22) → the oracle is SSE (P^prSBP = PC {SSE}, FP^prSBP = InFP SSE, OGTD[prSBP] = OGTD {SSE} Set.univ); instances are strings sseInst n s C m = 1ⁿ0 1ˢ0 code(C) bin(m) for a circuit C with n inputs and at most s gates; #C ≤ m/2 as 2·#C ≤ m; the no-set asks 2·#C ≤ m of every instance the string encodes; malformed strings and m = 0 are in neither set; reason: the paper's own identification of prSBP with its complete problem SSE (pp.22, 25); sseInst is injective on instances, so the no-set is the paper's, and every polynomial-time encoding of (C, m) gives the same classes
--   - encoding: "given any circuit V", "one can compute a … certificate with at most 3(a + b) + 1 elements" (computable = polynomial time with any fixed oracle consistent with SSE, §A.5, p.32) → InFP SSE of the relation: on input gwInput a b s V (a, b in unary, V with at most s gates) the output is a side bit (1 row-side, 0 column-side) followed by the certificate elements concatenated, a list E of at most 3(a + b) + 1 strings of length a (rows) or b (columns); other inputs may get any output; reason: FP^SSE is the paper's meaning of 'computable' in §A.5; a list of at most k entries is a set of at most k elements; with fixed element lengths the output determines the set (for a = 0 the only possible row-side certificate is {ε})
--   - reading: Theorem A.5.2 as printed on p.33 has no last sentence; its restatement Theorem 5.2 (p.12) adds "If V has an irrefutable row, the output is row-side" (proved for the same procedure as Corollary A.5.3) → the clause is included: HasIrrefutableRow a b V → the side bit is 1; reason: the main-text statement of the same theorem; the stronger of the two printed versions
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.5.2, p.33; Theorem 5.2, p.12; "computable", §A.5, p.32

import Mathlib
import Definitions.Def_KarpLiptonOM_InFP
import Definitions.Def_KarpLiptonOM_Supplement_SSE
import Definitions.Def_KarpLiptonOM_Supplement_gwInput
import Definitions.Def_KarpLiptonOM_Supplement_IsRowCert
import Definitions.Def_KarpLiptonOM_Supplement_IsColCert
import Definitions.Def_KarpLiptonOM_Supplement_HasIrrefutableRow

namespace KarpLiptonOM.Supplement

/-- Theorem A.5.2 (Goldreich–Wigderson lemma with approximate counting; Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.33), in the form of
Theorem 5.2 (p.12): given any circuit `V : {0,1}^a × {0,1}^b → {0,1}`, one can compute a row-side or
a column-side collectively irrefutable certificate with at most `3(a + b) + 1` elements; if `V` has
an irrefutable row, the output is row-side. "Computable" means in polynomial time with a fixed oracle
consistent with SSE, for every such oracle (§A.5, p.32): the search problem is in `FP^SSE`.

**Formalization Note** Strings, machines and classes are those of the published `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle (Definition A.2.1), lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. prSBP enters only through its complete problem SSE, as in the paper: `P^prSBP = PC {SSE}`, `FP^prSBP = InFP SSE`, `OGTD[prSBP] = OGTD {SSE} Set.univ` (pp.22, 25). The item's natural-language statement lists every difference from the page.

The input is `gwInput a b s V`; inputs encoding no circuit may get any output. The output is a side
bit (`true` = row-side, `false` = column-side) followed by the certificate's elements concatenated,
each of length `a` (rows) or `b` (columns). -/
theorem theorem_A_5_2 : InFP SSE (fun x out =>
    ∀ (a b s : ℕ) (V : Circuit (a + b)), V.gates.length ≤ s → x = gwInput a b s V →
      ∃ E : List (List Bool), E.length ≤ 3 * (a + b) + 1 ∧
        ((out = true :: E.flatten ∧ IsRowCert a b V E) ∨
          (out = false :: E.flatten ∧ IsColCert a b V E)) ∧
        (HasIrrefutableRow a b V → out.head? = some true)) := by sorry

end KarpLiptonOM.Supplement
