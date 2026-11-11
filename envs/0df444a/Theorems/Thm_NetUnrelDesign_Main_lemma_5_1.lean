-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_5_1
-- name    : NetUnrelDesign.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:44.091991+00:00
-- url     : https://prove2.me/theorems/9553ab5d-19c5-43d7-a369-c299ac67e34c
-- title:
--   Lemma 5.1 — preparation: a feasible x⁰ with u(x⁰) ≤ η, or x⁰, λ₀, J, x̄ with (5.2), (5.3), (5.6), in expected time (5.5)
-- statement:
--   There are an absolute constant $\gamma>0$, a constant $C>0$ and one program, which uses no oracle, such that the following holds for every instance satisfying (1.1) and every threshold $0<\eta<1$. Given the instance and $\eta$, on every halting run the program does one of two things:
--   - it returns a feasible $x^0$ with $u(x^0)\le\eta$; or
--   - it returns $x^0$, $\lambda_0$, a nonsingular matrix $J$ and a center $\bar x$ with $x^0\in X$, $\lambda_0=\lambda(x^0)$, (5.2) $\lambda_0\ge\Lambda-1$ where $\Lambda=\max_X\lambda$, (5.3) $\underline u:=e^{-(\lambda_0+1)}\le u^*$, $\underline u>\eta/(eM)$ and $u(x^0)\le eMu^*$, and
--   $$\bar x+JB_2\subseteq Q_0\subseteq\bar x+\gamma m^2JB_2,\tag{5.6}$$
--   where $Q_0=X\cap\{\lambda\ge\lambda_0-1-\log M\}$.
--
--   Its expected time is at most $C[km^2+m^3\log(2m)]\log(2m+\log(1/\eta))$ (5.5). The output is always correct; only the running time is random.
--
--   Differences from the source:
--
--   - encoding: "an algorithm … in expected time" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - reading: 'returns x0, λ0, and a nonsingular matrix J with center x̄ such that (5.2)–(5.3) hold' → also x⁰ ∈ X and λ₀ = λ(x⁰); reason: §5.1 defines x⁰ as the feasible point returned by the maximization and λ₀ = λ(x⁰); (5.2)–(5.3) are stated about these
--   - encoding: the two outcomes → integer output cell 0 is 0 for the threshold outcome and nonzero for the prepared outcome; reason: output layout
--   - encoding: γ an absolute constant → ∃ γ > 0 quantified before all instances; reason: uniformity made explicit
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 5.1, p. 16 (PDF 17); (5.2)–(5.3), p. 15 (PDF 16)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Lemma 5.1 (Preparation).** There are an absolute constant `γ > 0`, a constant `C > 0` and one
program (no oracle) such that, for every instance satisfying (1.1) and every threshold
`0 < η < 1`, the program, given the instance and `η`, on every halting run either returns
(integer output cell `0` equal to `0`) a feasible `x⁰` with `u(x⁰) ≤ η`, or returns (cell `0`
nonzero) `x⁰`, `λ₀`, a nonsingular `J` and a center `x̄` with `x⁰ ∈ X`, `λ₀ = λ(x⁰)`, (5.2),
(5.3) and (5.6) `x̄ + JB₂ ⊆ Q₀ ⊆ x̄ + γm²JB₂`; and its expected time is at most
`C[km² + m³ log(2m)] log(2m + log(1/η))` (5.5). The output is always correct; only the running time
is random. Sun 2026, p. 16 (PDF 17), with (5.2)–(5.3) on p. 15 (PDF 16). -/
theorem lemma_5_1 :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ {n m k : ℕ} (I : Instance n m k), I.Standing →
        ∀ η : ℝ, 0 < η → η < 1 →
          OnEveryHalt P noOracleFn (initState noOracle (instInts I) ([η] ++ instReals I))
              (fun s =>
                (outInt s 0 = 0 → outVec s 1 m ∈ I.feasible ∧ I.u (outVec s 1 m) ≤ η) ∧
                (outInt s 0 ≠ 0 →
                  PrepData I η γ (outVec s 1 m) (outReal s 0) (outMat s (1 + 2 * m) m)
                    (outVec s (1 + m) m))) ∧
          expectedWork P noOracleFn (initState noOracle (instInts I) ([η] ++ instReals I)) ≤
            ENNReal.ofReal (C * ((k : ℝ) * m ^ 2 + (m : ℝ) ^ 3 * Real.log (2 * m)) *
              Real.log (2 * m + Real.log (1 / η))) := by sorry

end NetUnrelDesign.Main
