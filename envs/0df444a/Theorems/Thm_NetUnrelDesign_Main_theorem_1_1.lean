-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_theorem_1_1
-- name    : NetUnrelDesign.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:36.842989+00:00
-- url     : https://prove2.me/theorems/9a2522fe-abba-4d93-a007-02a6c92ef561
-- title:
--   Theorem 1.1 — relative design from unreliability estimates: (1+ε)-optimal w.p. 1 − δ with Õ(m²ε⁻²log(2/δ)) oracle calls at accuracy 1/(8√n)
-- statement:
--   There are constants $C>0$ and $c\in\mathbb N$ and one program of the randomized real RAM with a scalar-unreliability-oracle instruction such that the following holds. Take any instance satisfying (1.1): a connected multigraph $G$ with $n\ge2$ vertices and $m$ labelled edges (loops and parallel edges allowed), $0<q^0_e\le1$, $A\in\mathbb R^{k\times m}$ with $A_{ij}>0$, $b>0$, $k\ge1$. Take any $0<\varepsilon,\delta\le1/2$. Take any oracle that answers every call $(H;\alpha,1/16)$, on every graph $H$, within a factor $1\pm\alpha$ of $u_H$ with probability at least $15/16$ on fresh randomness, where $\alpha=1/(8\sqrt n)$. Take any $T_0\ge m$ bounding the expected cost of such calls on graphs with at most $m$ edges and at most $n$ vertices. Given the instance, $\varepsilon$ and $\delta$, but not $u^*$, the program:
--   1. returns $\hat x\in X$ on every halting run;
--   2. halts with $u(\hat x)\le(1+\varepsilon)u^*$ with probability at least $1-\delta$;
--   3. calls the oracle only at relative accuracy $\alpha$ and failure probability $1/16$;
--   4. makes an expected number of oracle calls at most $C\,L^c\,m^2\varepsilon^{-2}\log(2/\delta)$;
--   5. has expected total work (its own steps plus the oracle's costs) at most
--   $$C\,P(u^*)+C\,L^c\,(m^2T_0+km^2)\,\varepsilon^{-2}\log(2/\delta).\tag{1.4}$$
--
--   Here $L=\log(2m(k+1)/\varepsilon)$ and $P(s)=(km^2+m^3\log(2m))\log(2m+\log(1/s))$ (1.3).
--
--   Differences from the source:
--
--   - generalization: the oracle U(H; s, β) is valid for every graph and every (s, β) → validity is required only for calls at (s, β) = (α, 1/16), on every graph; reason: clause 3 shows the program makes no other call; an oracle valid at every (s, β) satisfies the hypothesis
--   - encoding: Õ(·) suppresses factors logarithmic in m, k and 1/ε; O(P(u*)) → C·L^c with L = log(2m(k+1)/ε), and C·P(u*), with C > 0 and c ∈ ℕ fixed before all inputs and oracles; reason: the paper's Õ convention made explicit
--   - encoding: "there is an algorithm" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: T₀ = T_U(m, n, α, 1/16) ≥ m bounding the expected work of the oracle → any real T₀ ≥ m that bounds the expected cost of every call (H; α, 1/16) with H having at most m edges, at most n vertices and failure probabilities in [0, 1]; reason: T_U is by definition such a bound
--   - encoding: fresh randomness for every call; probabilities and expectations → the oracle is a measurable function of its query and its own fresh tape; probability and expectation are over the joint law of the machine tape and all oracle tapes, with non-halting counted as failure and as infinite work; reason: the oracle model of §1.1
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Theorem 1.1, p. 2 (PDF 3); proof p. 20 (PDF 21) and App. A.1, p. 21–23 (PDF 22–24)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Theorem 1.1 (Relative design from unreliability estimates).** There are constants `C > 0`,
`c ∈ ℕ` and one program of the randomized real RAM with a scalar-unreliability-oracle instruction
such that, for every instance satisfying (1.1) (connected multigraph, `n ≥ 2`, loops and parallel
edges allowed, `0 < q⁰_e ≤ 1`, `A_ij > 0`, `b_i > 0`, `k ≥ 1`), every `0 < ε, δ ≤ 1/2`, every
oracle that answers every call `(H; α, 1/16)` on every graph `H` within a factor `1 ± α` of `u_H`
with probability at least `15/16` on fresh randomness, `α = 1/(8√n)`, and every `T₀ ≥ m` bounding
the expected cost of such calls on graphs with at most `m` edges and at most `n` vertices: the
program, given the instance, `ε` and `δ` (not `u*`),
(i) returns `x̂ ∈ X` on every halting run;
(ii) halts with `u(x̂) ≤ (1 + ε)u*` with probability at least `1 − δ`;
(iii) calls the oracle only at accuracy `α` and failure probability `1/16`;
(iv) makes an expected number of calls at most `C L^c m² ε⁻² log(2/δ)`;
(v) has expected total work (its own steps plus oracle costs) at most
`C P(u*) + C L^c (m²T₀ + km²) ε⁻² log(2/δ)` (1.4),
where `L = log(2m(k+1)/ε)` and `P(s) = (km² + m³ log(2m)) log(2m + log(1/s))` (1.3).
Sun 2026, p. 2 (PDF 3). -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ, ∃ P : Program, Admissible P ∧
      ∀ {n m k : ℕ} (I : Instance n m k), I.Standing →
        ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
          ∀ O : Oracle scalarSpec, ScalarValidOn (fun Q => Q.AtParams (primAcc n) (1 / 16)) O →
            ∀ T0 : ℝ, (m : ℝ) ≤ T0 →
              ScalarCostOn (fun Q => Q.AtParams (primAcc n) (1 / 16) ∧ Q.Small n m) T0 O →
                OnEveryHalt P O (initState scalarSpec (instInts I) ([ε, δ] ++ instReals I))
                    (fun s => outVec s 0 m ∈ I.feasible) ∧
                failureProb P O (initState scalarSpec (instInts I) ([ε, δ] ++ instReals I))
                    (fun s => I.u (outVec s 0 m) ≤ (1 + ε) * I.uStar) ≤ ENNReal.ofReal δ ∧
                OnEveryState P O (initState scalarSpec (instInts I) ([ε, δ] ++ instReals I))
                    (fun s => ∀ c ∈ s.transcript, c.1.AtParams (primAcc n) (1 / 16)) ∧
                expectedCalls P O (initState scalarSpec (instInts I) ([ε, δ] ++ instReals I)) ≤
                  ENNReal.ofReal (C * Lrate m k ε ^ c * (m : ℝ) ^ 2 * ε⁻¹ ^ 2 *
                    Real.log (2 / δ)) ∧
                expectedWork P O (initState scalarSpec (instInts I) ([ε, δ] ++ instReals I)) ≤
                  ENNReal.ofReal (C * prepCost m k I.uStar +
                    C * Lrate m k ε ^ c * ((m : ℝ) ^ 2 * T0 + (k : ℝ) * m ^ 2) * ε⁻¹ ^ 2 *
                      Real.log (2 / δ)) := by sorry

end NetUnrelDesign.Main
