-- Prove2me | Theorems.Thm_NonmonotoneSubmod_RandomSet_Supplement_theorem_4_3
-- name    : NonmonotoneSubmod.RandomSet.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:18:18.937801+00:00
-- url     : https://prove2.me/theorems/713f266c-8eff-4208-83e3-dabb7d446883
-- title:
--   Theorem 4.3 — general succinct inapproximability
-- statement:
--   Fix any real $\varepsilon>0$. Suppose that, for every fixed bound on building-block arity, a deterministic algorithm runs in polynomial bit time and, on every nonnegative submodular succinct instance, outputs a subset $S$ satisfying
--   $$f(S)\ge\left(\frac34+\varepsilon\right)\max_T f(T).$$
--   Then $\mathrm P=\mathrm{NP}$. There is no symmetry, monotonicity or zero-empty-set-value assumption. The algorithm must work on arbitrary rational-table building blocks in each arity class, and is not restricted to the six-element gadgets. Thus an algorithm on the whole source class would also imply P = NP.
--
--   This companion is the general succinct-model hardness theorem, with Lemma 4.2 as its supporting result. It is not used to prove the published random-set guarantee.
--
--   **Formalization Note** The constants and positive-slack quantifier are exact. The polynomial machine and its degree may depend on fixed slack and arity but not on instance size. No PSD or PCP assumption is added to this theorem; those enter its proof through the structured reduction. Ratios above one remain included as in the source.
--
--   Differences from the source:
--   - generalization: succinct representation with finitely encoded coefficients → hardness already for every fixed arity class of arbitrary rational-table building blocks; reason: any polynomial algorithm on the full source class restricts to these inputs; the source reductions use rational tables, so this strengthens rather than weakens the hardness claim
--   - encoding: polynomial-time approximation unless P = NP → HasPolyApprox at the exact fixed ratio implies equality of the published binary-language classes P and NP; reason: actual deterministic Turing-machine time is polynomial in all input bits, with constants allowed to depend on the fixed slack and arity; binary languages express the standard P = NP conclusion
--   - encoding: finite labelled ground set and returned subset → Fin n labels and a sparse self-delimiting binary subset output; reason: finite relabelling and a standard polynomially related explicit representation; sparse output handles unused labels without an artificial output-length obstruction
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1147, Theorem 4.3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Succinct

namespace NonmonotoneSubmod.RandomSet.Supplement

theorem theorem_4_3 (ε : ℝ) (hε : 0 < ε)
    (hA : HasPolyApprox (3 / 4 + ε) false) :
    CookPvsNP.P Bool = CookPvsNP.NP Bool := by sorry

end NonmonotoneSubmod.RandomSet.Supplement
