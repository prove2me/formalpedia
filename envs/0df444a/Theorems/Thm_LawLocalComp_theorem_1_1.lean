-- Prove2me | Theorems.Thm_LawLocalComp_theorem_1_1
-- name    : LawLocalComp.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:16:21.699286+00:00
-- url     : https://prove2.me/theorems/a52f15f7-8e6d-4e55-9557-cff961eaebf8
-- title:
--   Theorem 1.1 (Principal compression frontiers)
-- statement:
--   **Setting.** A *law-local map* sees one finite nonnegative rational law and common parameters ($\varepsilon$ and the supplied resources), not the jobs, the other laws, the selection, the directions or the norm. For independent sizes $X_j$, nonnegative directions $a_j\in\mathbb R^d_+$ and a norm $g$ monotone on $\mathbb R^d_+$, write $L=\sum_jX_ja_j$ and $\tilde L=\sum_jY_ja_j$ with $Y_j=\Phi(X_j)$ sampled independently per copy. The contract is
--   $$\mathbb E g(\tilde L)\le\mathbb E g(L)\le(1+\varepsilon)\,\mathbb E g(\tilde L).\tag{1}$$
--   A horizon $N$ admits selections of at most $N$ jobs; a rank promise $q$ admits every finite selection with $\dim\operatorname{span}\{a_j\}\le q$; with both, $Q=\min\{N,q\}$; and $M=N$, $q$ or $\min\{N,q\}$. Put
--   $$J(\varepsilon,N,q)=\min\Big\{\sqrt{\tfrac{\log(N+1)\log(Q+1)}{\varepsilon}},\ \tfrac{\log(Q+1)}{\varepsilon}\Big\},\qquad A(\varepsilon,M)=\varepsilon^{-1}\log\big(1+\sqrt{\varepsilon\log(M+1)}\big).$$
--   The robust comparison is $(1+\varepsilon)^{-1}\mathbb E\|L\|_\infty\le\mathbb E\|\tilde L\|_\infty\le(1+\varepsilon)\mathbb E\|L\|_\infty$ (14).
--
--   **Theorem.** For rational $0<\varepsilon\le1$, rational law-local conditional-mean maps satisfy (1) with $O(\cdot)$ of the atom orders below; they preserve means and point masses and are computable in time polynomial in the input bits, $1/\varepsilon$ and the bit lengths of the supplied resources. The orders are matched by lower bounds:
--
--   | Laws and resources | Atom order | Matching lower |
--   |---|---|---|
--   | arbitrary, horizon $N\ge2$ | $\varepsilon^{-1/2}\log(N+1)$ | robust, $\varepsilon\le1/16384$ |
--   | arbitrary, rank $q\ge2$ only | $\varepsilon^{-1}\log(q+1)$ | robust, $\varepsilon\le1/1024$ |
--   | arbitrary, both, $Q\ge2$ | $J(\varepsilon,N,q)$ | actual conditional means, $\varepsilon\le2^{-40}$ |
--   | lattice-LC or conditional IFR, $M\ge2$ | $A(\varepsilon,M)$ | robust, $\varepsilon\le2^{-20}$ |
--
--   A robust lower bound holds for every map satisfying (14), with biased means and arbitrary outputs on constant inputs allowed; it counts positive output atoms. Horizon one or rank one is exact by the mean. For lattice-log-concave laws and every fixed $C>1$, the sharp atom order for distortion $C$ is $\Theta_C(1+\log\log(M+2))$, with a robust lower bound.
--
--   The statement is the conjunction of eleven clauses: the four uppers U1–U4, the four lowers L1–L4, exactness E, and the fixed-distortion upper F⁺ and lower F⁻. Every $O$/$\Omega$ constant is absolute; the $\Theta_C$ constants depend only on $C$.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` on binary encodings of the rational inputs, with a unary pad of length $\lceil1/\varepsilon\rceil$ as the only unary part. Uppers bound the number of all output atoms, lowers count positive output atoms.
--
--   Differences from the source:
--   - reading: polynomial in input bits, 1/ε and logarithmic supplied resources → one Turing machine (Mathlib's TM2ComputableInPolyTime) on binary rationals plus a unary pad of length ⌈1/ε⌉₊ (empty for the fixed-distortion upper, where C is fixed), correct on every list representing the input law; reason: the literal reading of 'polynomial in 1/ε and log N'; the pad is the only unary part
--   - reading: atom order and matching lower → uppers bound all output atoms, lowers bound positive output atoms; reason: the lowers count | supp(Y) \ {0} | as in (17) and (21); an upper for all atoms implies the one for positive atoms
--   - reading: the row 'Lattice-LC or conditional IFR' upper → one map on conditional-IFR laws, with (1) on selections of conditional-IFR laws; reason: every lattice-log-concave law is conditional IFR (Corollary 8.2, p.16), so this covers both classes
--   - generalization: robust lowers for law-local maps satisfying (14) → lowers for every function Φ from finite real laws to finite real laws satisfying (14), with no rationality or mean condition on outputs; reason: contains every rational map; specializes to the paper's maps
--   - generalization: row 3 lower for actual CM maps satisfying (1) → actual CM maps satisfying only the maximum-norm comparison (14) under both resources; reason: (1) implies (14); Theorem 6.2, p.10: 'The lower uses only maximum norms'
--   - generalization: row 4 lower for the classes lattice-LC or conditional IFR → the contract (14) is assumed only on selections of lattice-log-concave laws; reason: a map with the contract on conditional-IFR laws has it on their lattice-log-concave subclass
--   - generalization: Horizon one or rank one is exact by the mean (rational laws) → exactness for arbitrary finite real laws, plus the statement that the mean map is a rational CM map preserving means and point masses on rational laws; reason: specializes to rational laws
--   - reading: Θ_C(1 + log log(M + 2)) with no stated range of M → the fixed-distortion clauses for every resource with M ≥ 1; reason: at M = 0 no nonempty selection is admitted and a lower bound cannot hold; log log(M + 2) is the paper's expression
--   - encoding: laws, independence, log, ε^{-1/2}, O and Ω → finitely supported ℝ-valued laws with IsRatLaw, product weights, natural Real.log, 1/√ε, existential constants before every parameter; reason: Lean conventions; same instances
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2, with the model and (1)–(3) of §1, p.2, and the robust comparison (14), p.8

import Mathlib
import Definitions.Def_LawLocalComp_clauseU1
import Definitions.Def_LawLocalComp_clauseU2
import Definitions.Def_LawLocalComp_clauseU3
import Definitions.Def_LawLocalComp_clauseU4
import Definitions.Def_LawLocalComp_clauseL1
import Definitions.Def_LawLocalComp_clauseL2
import Definitions.Def_LawLocalComp_clauseL3
import Definitions.Def_LawLocalComp_clauseL4
import Definitions.Def_LawLocalComp_clauseE
import Definitions.Def_LawLocalComp_clauseFplus
import Definitions.Def_LawLocalComp_clauseFminus

namespace LawLocalComp

/-- **Theorem 1.1 (Principal compression frontiers).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2, with the model of §1, p.2 ((1)–(3)) and the robust comparison (14), p.8.

All eleven assertions of the theorem: the four polynomial-time upper bounds (horizon `N`, rank `q`,
both, and lattice-LC/conditional-IFR laws), the four matching lower bounds (robust for rows 1, 2 and 4,
actual conditional means for row 3), exactness of the mean at horizon or rank one, and for every fixed
`C > 1` the sharp order `Θ_C(1 + log log(M + 2))` on lattice-log-concave laws with a robust all-`C`
lower bound.

**Formalization Note.** Each row is a definition `clause…`; every `O`/`Ω` is an absolute constant
quantified before every parameter (`Θ_C` constants after `C`). Uppers count all output atoms, lowers
count positive output atoms. -/
theorem theorem_1_1 :
    clauseU1 ∧ clauseU2 ∧ clauseU3 ∧ clauseU4 ∧ clauseL1 ∧ clauseL2 ∧ clauseL3 ∧ clauseL4 ∧
      clauseE ∧ clauseFplus ∧ clauseFminus := by sorry

end LawLocalComp
