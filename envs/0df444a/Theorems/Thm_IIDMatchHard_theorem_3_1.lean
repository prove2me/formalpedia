-- Prove2me | Theorems.Thm_IIDMatchHard_theorem_3_1
-- name    : IIDMatchHard.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:16.700482+00:00
-- url     : https://prove2.me/theorems/d1892461-bdb7-4983-aee2-06f7204d0324
-- title:
--   Theorem 3.1 — approximating the online optimum of i.i.d. matching within $1\pm\varepsilon_0$ is NP-hard
-- statement:
--   For online stochastic matching with i.i.d. arrivals, there is a constant $\varepsilon_0>0$ such that approximating the online optimum within a factor $1\pm\varepsilon_0$ is NP-hard, even when the instance is unweighted and every type has exactly two neighbors.
--
--   Precisely, for every NP language $L$ there are a polynomial-time map $x\mapsto I_x$ into unweighted known-i.i.d. instances in which every type has exactly two neighbors, and a polynomial-time answer map, such that every rational $\bar V$ with
--   $$\big|\bar V-\mathrm{OPT}(I_x)\big|\ \le\ \varepsilon_0\,\mathrm{OPT}(I_x)$$
--   lets the answer map decide whether $x\in L$.
--
--   The online optimum is the value of the best online policy, the benchmark for "philosopher inequalities". The theorem shows it has no polynomial-time approximation scheme unless P = NP, in contrast with the polynomial-time constant-factor approximations of the optimum known for related problems.
--
--   Differences from the source:
--   - reading: "NP-hard" → ApproxNPHard: a polynomial-time reduction from every NP language over any finite nonempty alphabet that queries the approximation once, correct for every rational answer within the factor; reason: App. B.9 performs exactly such a reduction; it implies hardness under polynomial-time oracle reductions
--   - reading: "the instance" (unweighted, every type with exactly two neighbors) → Inst with two distinct listed neighbors per type and positive rational probabilities summing to one, binary-encoded by encInst; reason: inputs must be finite objects; positivity removes only types that never arrive, so the class is smaller and the claim stronger
--   - encoding: OPT(I) = sup over policies of E[M_π] → the real supremum over deterministic policies (functions of earlier types, matched set and current type) of the finite-sum value; reason: §2.1, p.4: a deterministic policy is optimal
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.1, p.5 (PDF p.6); proof in App. B.9, pp.22–23

import Definitions.Def_IIDMatchHard_Inst
import Definitions.Def_IIDMatchHard_ApproxNPHard

set_option autoImplicit false

namespace IIDMatchHard

/-- **Theorem 3.1.** For online stochastic matching with i.i.d. arrivals, there is a constant
`ε₀ > 0` such that approximating the online optimum within a factor `1 ± ε₀` is NP-hard, even
when the instance is unweighted and every type has exactly two neighbors. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Theorem 3.1,
p.5 (PDF p.6); proof in App. B.9, pp.22–23.

**Formalization Note.** Instances are `Inst`s (unweighted known-i.i.d. instances with two
distinct listed neighbors per type and positive rational probabilities summing to one,
`Inst.Valid`), binary-encoded by `encInst`; `onlineOpt` is the supremum of the expected number of
matches over deterministic policies. "NP-hard" is `ApproxNPHard`: every NP language reduces by a
polynomial-time instance map and a polynomial-time answer map that is correct for every rational
answer within the factor `1 ± ε₀` of the online optimum. -/
theorem theorem_3_1 : ∃ ε0 : ℝ, 0 < ε0 ∧ ApproxNPHard encInst Inst.Valid onlineOpt ε0 := by sorry

end IIDMatchHard
