-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_2_6
-- name    : MDPFinance.PDMDP.theorem_8_2_6
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:02.439988+00:00
-- url     : https://prove2.me/theorems/c0303ec3-7a0d-4a20-8eec-48fa81e0bd9e
-- title:
--   Theorem 8.2.6 — existence of an optimal relaxed Markov policy
-- statement:
--   This is the chapter's capstone existence theorem. Under a continuous upper bounding function $b$ with $c_Qc_\varphi < 1$ (standing in for the abstractly-defined $\alpha_b<1$, per Definition 8.2.4's own remark that $\alpha_b \le c_Qc_\varphi$) and the Continuity and Compactness Assumptions, the value function $J^{rel}_\infty$ of the discrete-time model embedded with **relaxed** controls is bounded (in $IB_b^+$), upper semicontinuous, and a genuine fixed point of the maximal-reward operator $T$ — and an optimal relaxed Markov policy $f : E \to R$ exists. The proof (not reproduced here) applies Lemma 8.2.5 to verify Theorem 7.2.1's own upper-semicontinuity hypotheses for the relaxed embedded model, then invokes that theorem's abstract existence conclusion directly.
--
--   **Formalization Note.** The optimal policy found here is *relaxed* — valued in $\mathbb P(U)$, not $U$ — and this is exactly the theorem's own content, not a weakening on this mission's part: recovering a genuine $U$-valued (nonrelaxed) optimal policy is the strictly harder claim of `theorem_8_2_7`, proved under extra hypotheses. Stating this goal with a $U$-valued policy instead would silently substitute Theorem 8.2.7's conclusion for Theorem 8.2.6's, the chapter-specific pitfall this mission's `BRIEF.md` flags explicitly, and is exactly the trivializing formalization this item avoids.
--
--   **Moderation note.** The draft's version of the main theorem stated a real fixed-point equation for an arbitrary map `J`, a supremum over arbitrary maps and no measurability of the maximizer, with the product topology on `R`; several of its clauses were junk-satisfiable. Now, under an upper bounding function, the continuity-and-compactness assumptions (Young topology) and standard Borel `E`, `U`: `J^r_∞ ∈ IB_b^+`, `J^r_∞` is upper semicontinuous, `J^r_∞ = T^r J^r_∞` in `[-∞,∞]`, and there is a *measurable* relaxed decision rule `f^*` attaining the supremum with `J^r_∞ = J^r_{(f^*)^∞}`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 253, PDF 264, Theorem 8.2.6

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Relaxed

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
  [TopologicalSpace.MetrizableSpace U] [SecondCountableTopology U] [StandardBorelSpace U]

/-- Theorem 8.2.6 (Bäuerle–Rieder, p. 253, PDF 264). Suppose the Piecewise Deterministic Markov
Decision Process has a continuous upper bounding function `b` with `α_b < 1` (`c_Q c_φ < 1`, the
book's bound `α_b ≤ c_Q c_φ`) and the Continuity and Compactness Assumptions are satisfied. Then
a) `J^{rel}_∞ ∈ IM_{usc}` (in `IB_b^+` and upper semicontinuous) and `J^{rel}_∞ = T J^{rel}_∞`;
b) there exists an optimal **relaxed** stationary Markov policy `π^*_t = f(Z_n)(t-T_n)` for a
measurable decision rule `f : E → R`. `E`, `U` are Borel spaces (`U` compact by the
assumptions). -/
theorem theorem_8_2_6 (Mk : PDMDPModel E U) (EmbR : EmbeddedKernelRelaxed Mk) (b : E → ℝ)
    (hb_cont : Continuous b) (cr cQ cφ : ℝ) (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hαb : cQ * cφ < 1) (hcc : ContinuityCompactnessAssumptions Mk b) :
    (JrelInfSup Mk EmbR ∈ IBbPlus b ∧ UpperSemicontinuous (JrelInfSup Mk EmbR) ∧
        ∀ x, JrelInfSup Mk EmbR x = Trel Mk EmbR (JrelInfSup Mk EmbR) x) ∧
      ∃ f : E → RelaxedControlFn U, Measurable f ∧
        ∀ x, JinfEmbedRelaxed Mk EmbR (fun _ => f) x = JrelInfSup Mk EmbR x := by sorry

end MDPFinance.PDMDP
