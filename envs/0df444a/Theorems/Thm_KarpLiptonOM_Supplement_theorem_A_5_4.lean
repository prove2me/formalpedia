-- Prove2me | Theorems.Thm_KarpLiptonOM_Supplement_theorem_A_5_4
-- name    : KarpLiptonOM.Supplement.theorem_A_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:43:42.582905+00:00
-- url     : https://prove2.me/theorems/d15d3d64-270c-4ef9-8b7b-e10f641d9caf
-- title:
--   Theorem A.5.4 (= Theorem 3) — $\mathrm P^{\mathrm{prS}^{\mathrm P}_2}\subseteq\mathrm P^{\mathrm{prSBP}}$ with FP and OGTD analogues; $\mathrm S^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}}$
-- statement:
--   Let SSE be the approximate-counting promise problem, complete for $\mathrm{prSBP}$, so that $\mathrm P^{\mathrm{prSBP}}=\mathrm P^{\mathrm{SSE}}$, $\mathrm{FP}^{\mathrm{prSBP}}=\mathrm{FP}^{\mathrm{SSE}}$ and $\mathrm{OGTD}[\mathrm{prSBP}]=\mathrm{OGTD}[\mathrm{SSE}]$. Then:
--
--   1. for every $\Pi\in\mathrm{prS}^{\mathrm P}_2$ there is a deterministic polynomial-time oracle machine $G$ such that, for every language $O$ consistent with SSE, the language decided by $G^O$ is consistent with $\Pi$;
--   2. $\mathrm P^{\mathrm{prS}^{\mathrm P}_2}\subseteq\mathrm P^{\mathrm{prSBP}}$;
--   3. $\mathrm{FP}^{\mathrm{prS}^{\mathrm P}_2}\subseteq\mathrm{FP}^{\mathrm{prSBP}}$;
--   4. $\mathrm{OGTD}[\mathrm{prS}^{\mathrm P}_2]\subseteq\mathrm{OGTD}[\mathrm{prSBP}]$;
--   5. in particular,
--
--   $$
--   \mathrm S^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}} .
--   $$
--
--   Here $\mathrm P^{\mathcal C}$ and $\mathrm{FP}^{\mathcal C}$ are unions over the promise problems of $\mathcal C$, with oracle access through every consistent language, and $\mathrm{OGTD}[\mathcal C]$ is the class of languages with polynomial-size advice computable from $1^n$ in $\mathrm{FP}^{\Pi}$ for some $\Pi\in\mathcal C$ and decoded in polynomial time. This strengthens $\mathrm S^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prAM}}$ of Chakaravarthy and Roy, since $\mathrm{prSBP}\subseteq\mathrm{prAM}$, and the authors' earlier $\mathrm L^{\mathrm P}_2\subseteq\mathrm P^{\mathrm{prSBP}}$.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 not imposed), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention of the published base definitions; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: prSBP oracle; SSE with yes-instances (C, m), #C ≥ m, and no-instances (C, m), #C ≤ m/2, m ≥ 1 in binary (p.22) → the oracle is SSE (P^prSBP = PC {SSE}, FP^prSBP = InFP SSE, OGTD[prSBP] = OGTD {SSE} Set.univ); instances are strings sseInst n s C m = 1ⁿ0 1ˢ0 code(C) bin(m) for a circuit C with n inputs and at most s gates; #C ≤ m/2 as 2·#C ≤ m; the no-set asks 2·#C ≤ m of every instance the string encodes; malformed strings and m = 0 are in neither set; reason: the paper's own identification of prSBP with its complete problem SSE (pp.22, 25); sseInst is injective on instances, so the no-set is the paper's, and every polynomial-time encoding of (C, m) gives the same classes
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.5.4 (Theorem 3), p.33; Theorem 3, p.5

import Mathlib
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_InFP
import Definitions.Def_KarpLiptonOM_PC
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_Consistent
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_tupleEnc
import Definitions.Def_KarpLiptonOM_Supplement_SSE
import Definitions.Def_KarpLiptonOM_Supplement_prSP2
import Definitions.Def_KarpLiptonOM_Supplement_SP2

namespace KarpLiptonOM.Supplement

/-- Theorem A.5.4 (= Theorem 3; Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.33, and p.5): for every `Π ∈ prS₂^P` there is a deterministic
polynomial-time oracle machine `G` such that, for every language `O` consistent with SSE, the language
decided by `G^O` is consistent with `Π`. Consequently `P^{prS₂^P} ⊆ P^prSBP`,
`FP^{prS₂^P} ⊆ FP^prSBP` and `OGTD[prS₂^P] ⊆ OGTD[prSBP]`. In particular, `S₂^P ⊆ P^prSBP`.

**Formalization Note** Strings, machines and classes are those of the published `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle (Definition A.2.1), lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. prSBP enters only through its complete problem SSE, as in the paper: `P^prSBP = PC {SSE}`, `FP^prSBP = InFP SSE`, `OGTD[prSBP] = OGTD {SSE} Set.univ` (pp.22, 25). The item's natural-language statement lists every difference from the page.

The five conjuncts are, in order: the machine `G`; `P^{prS₂^P} ⊆ P^SSE`; every search relation in
`FP^Π` for some `Π ∈ prS₂^P` is in `FP^SSE`; `OGTD[prS₂^P] ⊆ OGTD[SSE]`; `S₂^P ⊆ P^SSE`. -/
theorem theorem_A_5_4 :
    (∀ PP ∈ prSP2, ∃ (G : OracleTM) (k : ℕ), G.IsPolyTime k ∧
      ∀ O, Consistent O SSE → Consistent {q | G.Accepts O (tupleEnc [q])} PP) ∧
    PC prSP2 ⊆ PC {SSE} ∧
    (∀ R : List Bool → List Bool → Prop, (∃ PP ∈ prSP2, InFP PP R) → InFP SSE R) ∧
    OGTD prSP2 Set.univ ⊆ OGTD {SSE} Set.univ ∧
    SP2 ⊆ PC {SSE} := by sorry

end KarpLiptonOM.Supplement
