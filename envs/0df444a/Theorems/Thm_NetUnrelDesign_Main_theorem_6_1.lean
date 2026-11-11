-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_theorem_6_1
-- name    : NetUnrelDesign.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:31.116786+00:00
-- url     : https://prove2.me/theorems/6027e08d-b7d6-473a-83b1-4595da074f23
-- title:
--   Theorem 6.1 — optimization from marked estimates: (1+ε)-optimal w.p. 1 − δ in expected work (6.1)
-- statement:
--   For every marked-source constant $C_Z$, there are a constant $C$ and one program with a marked-source instruction such that the following holds. Take any instance satisfying (1.1), any $0<\varepsilon,\delta\le1/2$, and any marked source that satisfies (3.1) with $C_Z$ at every design, with fresh randomness at every call. Let $Q\ge m$ bound its expected cost at the direct queries of the bounded-domain method, that is, at every feasible point of risk at least $\varepsilon^2/(e^22^{30}m^8)$. Given the instance, $\varepsilon$ and $\delta$, but not $u^*$, the program
--   - returns $\hat x\in X$ on every halting run;
--   - halts with $u(\hat x)\le(1+\varepsilon)u^*$ with probability at least $1-\delta$;
--   - has expected work at most
--   $$C\,P(u^*)+C\bigl[m^3L^4+(mQ+km^2)\varepsilon^{-2}L^4h\bigr]\log(2/\delta).\tag{6.1}$$
--
--   Differences from the source:
--
--   - reading: 'at complete conditional expected cost at most Q ≥ m on the direct queries of the bounded-domain method' → expected cost ≤ Q at every feasible x with u(x) ≥ ε²/(e²2³⁰m⁸); reason: App. A.1 (p. 23, PDF 24): every direct numerator, normalizer and final value is evaluated at a feasible point of risk at least this floor; no cost bound elsewhere is assumed
--   - encoding: fresh marked estimates satisfying (3.1), C_Z an absolute constant → a measurable oracle of the design and its own fresh tape, valid for (3.1) at every design x ≥ 0; C_Z quantified before the program and C; reason: (3.1) is required at every design the method may query
--   - encoding: "there is an algorithm returning x̂ ∈ X" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: Pr{u(x̂) ≤ (1+ε)u*} ≥ 1 − δ → the set of runs that do not halt with u(x̂) ≤ (1+ε)u* has measure at most δ; reason: non-halting counts as failure
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Theorem 6.1, p. 18 (PDF 19); proof p. 19–20 (PDF 20–21)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Theorem 6.1 (Optimization from marked estimates).** For every marked-source constant `C_Z`
there are a constant `C` and one program with a marked-source instruction such that, for every instance
satisfying (1.1), every `0 < ε, δ ≤ 1/2`, every marked source satisfying (3.1) with `C_Z`
at every design (fresh randomness per call) and every `Q ≥ m` bounding its expected cost at the
direct queries of the bounded-domain method (every feasible point of risk at least the floor
`ε²/(e²2³⁰m⁸)` of (5.9)): the program, given the instance, `ε` and `δ` (not `u*`), returns
`x̂ ∈ X` on every halting run, halts with `u(x̂) ≤ (1 + ε)u*` with probability at least `1 − δ`,
and has expected work at most `C P(u*) + C[m³L⁴ + (mQ + km²)ε⁻²L⁴h] log(2/δ)` (6.1).
Sun 2026, p. 18 (PDF 19). -/
theorem theorem_6_1 :
    ∀ CZ : ℝ, 0 < CZ →
      ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
        ∀ {n m k : ℕ} (I : Instance n m k), I.Standing →
          ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
            ∀ (O : Oracle (markedSpec n m)) (Q : ℝ), MarkedValid I.ends I.q0 CZ O → (m : ℝ) ≤ Q →
              (∀ x ∈ I.feasible, riskFloor m ε ≤ I.u x → MarkedCostAt Q O x) →
                OnEveryHalt P O (initState (markedSpec n m) (instInts I) ([ε, δ] ++ instReals I))
                    (fun s => outVec s 0 m ∈ I.feasible) ∧
                failureProb P O (initState (markedSpec n m) (instInts I) ([ε, δ] ++ instReals I))
                    (fun s => I.u (outVec s 0 m) ≤ (1 + ε) * I.uStar) ≤ ENNReal.ofReal δ ∧
                expectedWork P O
                    (initState (markedSpec n m) (instInts I) ([ε, δ] ++ instReals I)) ≤
                  ENNReal.ofReal (C * prepCost m k I.uStar +
                    C * ((m : ℝ) ^ 3 * Lrate m k ε ^ 4 +
                      ((m : ℝ) * Q + (k : ℝ) * m ^ 2) * ε⁻¹ ^ 2 * Lrate m k ε ^ 4 * logTwoM m) *
                      Real.log (2 / δ)) := by sorry

end NetUnrelDesign.Main
