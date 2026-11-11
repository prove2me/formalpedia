-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_A_1
-- name    : NetUnrelDesign.Main.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:10:39.026142+00:00
-- url     : https://prove2.me/theorems/ea86782c-550e-4812-90f9-114a63de94cb
-- title:
--   Lemma A.1 — scalar estimates to marked records: an exact marked source with 0 ≤ Z ≤ 2, EZ² ≤ 5u², cost (A.1)
-- statement:
--   There are a constant $C$ and one program with a scalar-unreliability-oracle instruction such that the following holds. Take the paper's network $G$, connected with $n\ge2$ vertices and $m$ edges, with independent failure probabilities $q\in[0,1]^m$; a known $0<\eta\le u$; and a scalar oracle that gives fresh relative estimates on every iterated deletion/contraction minor of $G$ with inherited probabilities. At the primitive parameters $\alpha=1/(8\sqrt n)$ and $1/16$ its answer is within a factor $1\pm\alpha$ except with probability $1/16$. Let $T_0\ge m$ bound the expected cost of every such call. Given $G$, $q$ and $\eta$, the program is a marked source: its output weight $Z$ and partition $\Pi$ satisfy
--   $$\mathbb E[Z\varphi(\Pi)]=\mathbb E[1_{K\ge2}\varphi(\Pi)]\ \text{ for every bounded }\varphi,\qquad0\le Z\le2,\qquad\mathbb EZ^2\le5u^2.$$
--   It calls the oracle only at the primitive parameters and only on such minors, making at most $C\,m\log(m/\eta)$ primitive calls. Its expected work is $Q\le C(mT_0\log(m/\eta)+m^2)$ (A.1). No unbiasedness or moment assumption on the scalar answers is needed.
--
--   Differences from the source:
--
--   - reading: 'a graph with at most m original records and n vertices, with independent failure probabilities' → the paper's network (connected, n ≥ 2) with its m edges and any failure probabilities q ∈ [0,1]^m; reason: the lemma is applied to G (§1 standing assumption); with the edge count itself as m the statement implies the 'at most m' form, since its bounds increase with m and T₀ ≥ m weakens as m decreases
--   - reading: 'using O(m log(m/η)) primitive calls' → on every run, at most C·m·log(m/η) calls, all at (α, 1/16) and on iterated deletion/contraction minors of G with inherited probabilities; reason: the proof makes at most 2m amplified estimates, each a median of O(log(m/η)) primitive calls on minors
--   - encoding: a scalar oracle with fresh relative estimates on minors at α, 1/16; T₀ bounds the cost of every such call → validity and cost hypotheses required exactly at the queries (α, 1/16) whose graph is such a minor; the oracle is a measurable function of the query and its own fresh tape; reason: the oracle model of §1.1 restricted to the calls the lemma speaks of
--   - encoding: "there is a marked source … using … expected work" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: E[Zφ(Π)] = E[1_{K≥2}φ(Π)] → Z·φ(Π) is integrable under the joint law of machine and oracle tapes, and its integral equals Σ_F Pr(F)·1{disconnected}·φ(Π_F); Z and Π are read from the halted state (Z = 0 if the run does not halt, a null event); reason: Bochner integral with integrability stated, so no junk value
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma A.1, p. 21 (PDF 22); proof p. 22–23 (PDF 23–24)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces

open scoped BigOperators ENNReal Classical

namespace NetUnrelDesign.Main

/-- **Lemma A.1 (Scalar estimates to marked records).** There are a constant `C` and one program
with a scalar-unreliability-oracle instruction such that, for the connected multigraph `G`
(`n ≥ 2` vertices, `m` edges) with independent failure probabilities `q ∈ [0,1]^m`, every known
`0 < η ≤ u`, every scalar oracle giving fresh relative estimates (within a factor `1 ± α` except
with probability `1/16`, `α = 1/(8√n)`) on every iterated deletion/contraction minor of `G`, and
every `T₀ ≥ m` bounding the expected cost of every such call: the program, given `G`, `q` and `η`,
is a marked source — its output weight `Z` and partition `Π` satisfy `E[Zφ(Π)] = E[1_{K≥2}φ(Π)]`
for every bounded `φ`, `0 ≤ Z ≤ 2` on every halting run, and `E Z² ≤ 5u²` — it calls the oracle
only at the primitive parameters `(α, 1/16)` and only on such minors, on every run it makes
at most `C m log(m/η)` primitive calls, and its expected work is at most `C(mT₀ log(m/η) + m²)` (A.1).
Sun 2026, p. 21 (PDF 22). -/
theorem lemma_A_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ), 2 ≤ n → IsConnectedGraph ends →
        (∀ e, 0 ≤ q e ∧ q e ≤ 1) →
        ∀ η : ℝ, 0 < η → η ≤ unrel ends q →
          ∀ O : Oracle scalarSpec,
            ScalarValidOn (fun Q => Q.AtParams (primAcc n) (1 / 16) ∧ Q.MinorOf ends q) O →
            ∀ T0 : ℝ, (m : ℝ) ≤ T0 →
              ScalarCostOn (fun Q => Q.AtParams (primAcc n) (1 / 16) ∧ Q.MinorOf ends q) T0 O →
                OnEveryHalt P O (initState scalarSpec (graphInts ends) ([η] ++ vecList q))
                    (fun s => 0 ≤ outReal s 0 ∧ outReal s 0 ≤ 2) ∧
                OnEveryState P O (initState scalarSpec (graphInts ends) ([η] ++ vecList q))
                    (fun s => ∀ c ∈ s.transcript,
                      c.1.AtParams (primAcc n) (1 / 16) ∧ c.1.MinorOf ends q) ∧
                (∀ φ : Setoid (Fin n) → ℝ, BoundedFn φ →
                  MeasureTheory.Integrable (fun ω =>
                      outReal (finalState P O
                        (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω) 0 *
                      φ (partitionOfLabels fun v : Fin n => outInt (finalState P O
                        (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω) v))
                    jointLaw ∧
                  ∫ ω, outReal (finalState P O
                        (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω) 0 *
                      φ (partitionOfLabels fun v : Fin n => outInt (finalState P O
                        (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω) v)
                    ∂jointLaw =
                    expect q fun F => if Disconnected ends F then φ (partitionOf ends F) else 0) ∧
                ∫⁻ ω, ENNReal.ofReal (outReal (finalState P O
                    (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω) 0 ^ 2)
                  ∂jointLaw ≤ ENNReal.ofReal (5 * unrel ends q ^ 2) ∧
                (∀ ω, totalCalls P O (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ω ≤
                  ENNReal.ofReal (C * m * Real.log (m / η))) ∧
                expectedWork P O (initState scalarSpec (graphInts ends) ([η] ++ vecList q)) ≤
                  ENNReal.ofReal (C * ((m : ℝ) * T0 * Real.log (m / η) + (m : ℝ) ^ 2)) := by sorry

end NetUnrelDesign.Main
