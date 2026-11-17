-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_5
-- name    : MultitaskContracts.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:08:21.266257+00:00
-- url     : https://prove2.me/theorems/775e7305-8c85-4a76-a0f3-3033b512988b
-- title:
--   Theorem 5 — deciding $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}>B$ for independent tasks with rational data is NP-hard
-- statement:
--   Given an instance with independent tasks and a rational budget $B$, it is NP-hard to decide whether
--   $$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}\;>\;B.$$
--   Precisely, the instance is given by rational parameters $p_k,q_k,c_k$ in binary. The language of the binary codes of the inputs $(n;\,p,q,c;\,B)$ that describe an independent instance on $n$ tasks with $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}>B$ is **NP-hard**: every language in NP, over any finite nonempty alphabet, reduces to it by a polynomial-time many-one reduction.
--
--   Consequently, finding an optimal Min-Budget contract is NP-hard for heterogeneous independent tasks, and Budgeted Min-Pay cannot be approximated within any factor.
--
--   **Formalization Note** NP, polynomial-time computable functions and many-one reductions are those of the published `CookPvsNP_defs` (one-tape Turing machines, following Cook's Clay problem description). The language is `MinBudgetLang`, defined in this supplement.
--
--   Differences from the source:
--   - reading: "it is NP-hard to decide", no machine model named → ∀ finite nonempty Sym' and L' ∈ CookPvsNP.NP Sym', CookPvsNP.PolyReducible L' MinBudgetLang (one-tape Turing machines); reason: the standard definition of NP-hardness under polynomial-time many-one reductions; the paper's reduction is a polynomial-time map
--   - encoding: an instance with independent tasks and a rational budget B → binary codes over Option Bool of (n; p_k, q_k, c_k; B) with rationals in lowest terms; non-codes and invalid parameters are outside the language; OPT > B compared in EReal; reason: "rationals of polynomial bit length" (proof of Theorem 5) fixes the input size as the bit length; validity is checkable in polynomial time, and EReal makes the comparison exact for every B
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 5, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_MultitaskContracts_Supplement_MinBudgetLang

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 5** (§5.2, p.32, PDF 34). Given an instance with independent tasks and a rational
budget `B`, it is NP-hard to decide whether `OPT^Bun_MinBudget > B`: every language in NP, over
any finite nonempty alphabet, polynomial-time many-one reduces to `MinBudgetLang`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 5, p.32.

**Formalization Note.** NP, polynomial-time computability and many-one reductions are those of
the published `CookPvsNP_defs` (one-tape Turing machines, Cook's Clay description); the paper
names no machine model, and NP-hardness is read as the standard "every NP language reduces".
`MinBudgetLang` is the set of binary codes (alphabet `Option Bool`) of inputs `(n; p, q, c; B)`
with rational parameters of an independent instance on `n` tasks and `OPT^Bun_MinBudget > B`. -/
theorem theorem_5 :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
      L' ∈ CookPvsNP.NP Sym' → CookPvsNP.PolyReducible L' MinBudgetLang := by sorry

end MultitaskContracts.Supplement
