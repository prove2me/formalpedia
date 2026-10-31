-- Prove2me | Theorems.Thm_MissionAbort_decisionRule_of_costToGo
-- name    : MissionAbort.decisionRule_of_costToGo
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:54:22.732164+00:00
-- url     : https://prove2.me/theorems/4f2a47a4-f520-4347-822a-748cbea88645
-- title:
--   Appendix A.2: the optimal rules are determined by comparing the costs-to-go
-- statement:
--   Let $\mu$ be a probability law carrying a state process $S$ and signals $Y$ such that the failed state is absorbing on the decision grid and $Y_n=0$ exactly when $S(n\delta)$ is failed, almost surely. Let $a$ be an admissible rule family that compares the two costs-to-go at every history of positive probability in $[K]^n$, $n\in[N-1]$. Then $a$ minimizes the expected cost among admissible rule families, and
--   $$
--   \mathbb E\big[C(S(\mathfrak T+w_{\mathfrak T/\delta}),\mathfrak T)\big]=\mathbb C_c(0,\langle\rangle).
--   $$
--
--   This is the dynamic programming principle for the abort problem. It applies to both the original and the surrogate system, and it is what ties the costs-to-go to Problems (1) and (7).
--
--   Differences from the source:
--   - generalization: $a^*_n(y)=\mathbb 1\{\mathbb C_{ab}(n,y)<\mathbb C_c(n,y)\}$ → any admissible rule with $a_n(y)=1\Rightarrow\mathbb C_{ab}\le\mathbb C_c$ and $a_n(y)=0\Rightarrow\mathbb C_c\le\mathbb C_{ab}$ at positive-probability histories in $[K]^n$; reason: the printed strict rule is one such tie-break; the smallest-$\mathfrak T^*$ stipulation is another
--   - generalization: the original and the surrogate systems → any system with an absorbing, self-announcing failed state; reason: both systems satisfy this
--   - encoding: the value of the problem → $\mathbb C_c(0,\langle\rangle)$; reason: Problems (1) and (7) have no decision at time $0$, so the value of (9) at $n=0$ would add an abort option that the problems do not have
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, Appendix A.2, p.EC.2, "can be determined by comparing the two costs-to-go"

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model
import Definitions.Def_MissionAbort_state
import Definitions.Def_MissionAbort_clusterProcess
import Definitions.Def_MissionAbort_IsSignalSystem
import Definitions.Def_MissionAbort_Rule
import Definitions.Def_MissionAbort_IsAdmissible
import Definitions.Def_MissionAbort_expectedCost
import Definitions.Def_MissionAbort_IsMinimizer
import Definitions.Def_MissionAbort_value
import Definitions.Def_MissionAbort_costContinue
import Definitions.Def_MissionAbort_IsSeqOptimal

open MeasureTheory ProbabilityTheory Filter Topology

namespace MissionAbort

/-- **The rules are determined by comparing the costs-to-go** (Sun, Hu & Ye, arXiv:2505.03225v1,
Appendix A.2, p.EC.2, "can be determined by comparing the two costs-to-go"). For a state-signal system
with an absorbing, self-announcing failed state, an admissible rule family that compares the two
costs-to-go at every positive-probability history in `[K]ⁿ` solves the abort problem, and its value is
`Cc(0, ⟨⟩)`.

**Formalization Note.** The page writes `a∗ₙ(y) = 𝟙{Cab(n, y) < Cc(n, y)}`. `IsSeqOptimal` allows any
tie-break. This applies to the original system and, with `clusterProcess`, to the surrogate. -/
theorem decisionRule_of_costToGo {K : ℕ} (M : Model K) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℝ → Ω → Cluster) (Y : ℕ → Ω → Fin (K + 1))
    (hsys : IsSignalSystem M μ S Y) (a : Rule K) (ha : IsAdmissible M.N a)
    (hopt : IsSeqOptimal M μ S Y a) :
    IsMinimizer M μ S Y a ∧
      expectedCost M μ S Y a = costContinue M μ S Y 0 (fun i => i.elim0) := by sorry

end MissionAbort
