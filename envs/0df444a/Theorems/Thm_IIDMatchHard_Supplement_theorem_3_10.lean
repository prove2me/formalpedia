-- Prove2me | Theorems.Thm_IIDMatchHard_Supplement_theorem_3_10
-- name    : IIDMatchHard.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:21:35.453169+00:00
-- url     : https://prove2.me/theorems/b46822b6-85a3-499d-8cab-b1357d8aac76
-- title:
--   Theorem 3.10 — randomized hardness unless $\mathrm{NP}\subseteq\mathrm{BPP}$
-- statement:
--   There is a constant $\varepsilon_0>0$ that simultaneously witnesses the approximation hardness of Theorem 3.1 on valid unweighted known-i.i.d. matching instances with exactly two distinct neighbors per type and has both following randomized consequences:
--
--   1. If a randomized polynomial-time algorithm returns, on every such instance $I$, a rational $\bar V$ satisfying
--      $$
--      |\bar V-\operatorname{OPT}(I)|\le \varepsilon_0\operatorname{OPT}(I)
--      $$
--      with probability at least $2/3$, then $\mathrm{NP}\subseteq\mathrm{BPP}$.
--   2. If a randomized polynomial-time algorithm outputs, on every such instance, a polynomial-time online policy whose expectation jointly over the algorithm's coins and the i.i.d. arrivals is at least
--      $$
--      (1-\varepsilon_0/2)\operatorname{OPT}(I),
--      $$
--      then $\mathrm{NP}\subseteq\mathrm{BPP}$.
--
--   Thus, unless $\mathrm{NP}\subseteq\mathrm{BPP}$, neither randomized algorithm exists.
--
--   **Formalization Note** The same existential $\varepsilon_0$ is conjoined with the published `ApproxNPHard encInst Inst.Valid onlineOpt` property, so it is not an unrelated constant. Probabilities are exact counts of polynomially many fair seeds; every branch has a uniform polynomial runtime bound. The second expectation is not required to hold for each output policy separately.
--
--   Differences from the source:
--   - encoding: “the constant $\varepsilon_0$ and the instances of Theorem 3.1” → one existential $\varepsilon_0$ conjoined with the published `ApproxNPHard` property and both randomized implications; reason: this makes the shared witness and exact published instance class explicit
--   - encoding: “unless $\mathrm{NP}\subseteq\mathrm{BPP}$, no algorithm” → existence of either algorithm implies $\mathrm{NP}\subseteq\mathrm{BPP}$; reason: this is the logically equivalent contrapositive and does not assert a complexity separation
--   - encoding: randomized polynomial time and probability at least $2/3$ → one finite multitape machine with an explicit polynomial fair-coin count, a worst-case polynomial clock on every seed, and exact seed counting; reason: standard finite-machine encoding of the source's randomized algorithms
--   - encoding: “approximates the online optimum” → the approximation machine outputs a self-delimiting binary-encoded rational; reason: a polynomial-time algorithm has a finite charged output, and the reduction uses only rational approximations
--   - encoding: “outputs ... a polynomial-time online policy” → a finite output code interpreted by one uniform polynomial-time policy evaluator; reason: standard executable encoding that charges construction and online evaluation time
--   - encoding: $\mathrm{NP}\subseteq\mathrm{BPP}$ over finite alphabets → the inclusion for Boolean encodings; reason: standard polynomial-time binary encodings preserve both classes
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11); proof p.24 (PDF p.25)

import Mathlib
import Definitions.Def_IIDMatchHard_ApproxNPHard
import Definitions.Def_IIDMatchHard_Supplement_NPSubsetBPP
import Definitions.Def_IIDMatchHard_Supplement_RandPolicyGuarantee

set_option autoImplicit false

namespace IIDMatchHard

namespace Supplement

/-- **Theorem 3.10** (Teng, Yang, *Computational Hardness of Online Stochastic Matching*,
manuscript of Nov. 3, 2026, sha256 f0193d92…, p.10, PDF p.11; proof p.24, PDF p.25). For the
same positive constant `ε₀` and the same valid unweighted two-neighbor known-i.i.d. instance
class as Theorem 3.1, either (i) a randomized polynomial-time `(1 ± ε₀)` approximation that
succeeds with probability at least `2/3` on every instance, or (ii) a randomized polynomial-time
constructor whose polynomial-time online policies have joint expected value at least
`(1 - ε₀/2) OPT`, would imply `NP ⊆ BPP`.

**Formalization Note.** Conjoining the published `ApproxNPHard` property before both implications
binds one `ε₀` witness to Theorems 3.1 and 3.10. Approximation success is counted over the
algorithm's fair coins. The policy guarantee averages jointly over constructor coins and i.i.d.
arrivals; it is not required seed by seed. -/
theorem theorem_3_10 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ApproxNPHard encInst Inst.Valid onlineOpt ε₀ ∧
      ((∃ A : RandRatAlg,
          ∀ I : Inst, I.Valid →
            SucceedsTwoThirds A (encInst I) (fun q =>
              |(q : ℝ) - onlineOpt I| ≤ ε₀ * onlineOpt I)) → NPSubsetBPP) ∧
      ((∃ (E : PolicyInterpreter) (A : RandPolicyConstructor),
          RandPolicyGuarantee ε₀ E A) → NPSubsetBPP) := by sorry

end Supplement

end IIDMatchHard
