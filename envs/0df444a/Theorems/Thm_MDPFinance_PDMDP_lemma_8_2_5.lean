-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_lemma_8_2_5
-- name    : MDPFinance.PDMDP.lemma_8_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:01.130014+00:00
-- url     : https://prove2.me/theorems/84ea81c5-78c6-4b12-8f69-8033221670ea
-- title:
--   Lemma 8.2.5 — upper semicontinuity is preserved by the flow integral
-- statement:
--   This lemma is the technical core of Theorem 8.2.6's proof: given a continuous upper bounding function $b$ and an upper semicontinuous $w : E \times U \to \mathbb R$ with $w(x,u) \le c_wb(x)$, the flow-integrated, relaxed-control-averaged quantity $(x,\alpha) \mapsto \int_0^\infty e^{-(\beta+\lambda)t}\int_U w(\varphi\mathrm{Rel}^\alpha_t(x),u)\,\alpha_t(du)\,dt$ remains upper semicontinuous on $E \times R$. The book's proof (approximating $w$ from above by a decreasing sequence of bounded continuous functions, via Dini-type machinery for usc functions) is not reproduced here; only the statement is formalized. `statements.jsonl`'s extraction of this lemma cuts off mid-sentence after "Then"; the full statement above is read directly from the PDF.
--
--   **Formalization Note.** Hypotheses (ii)/(iii) are passed as the corresponding named hypotheses of `ContinuityCompactnessAssumptions` rather than that whole bundled Prop, since this lemma needs only those two of the five standing assumptions.
--
--   **Moderation note.** The draft stated upper semicontinuity of `(x,α) ↦ ∫_0^∞ e^{-(β+λ)t} ∫_U w(φ_t^α(x),u) α_t(du) dt` for the *product topology* on `R` (false in general; the book's claim is for the Young topology), took the integrals as real Bochner integrals and gave `w` no bound. Now the assumptions (ii)–(iii) of §8.2 are stated in the Young topology, `w` is upper semicontinuous with `w ≤ c_w b`, and the conclusion is upper semicontinuity of the `[-∞,∞]`-valued double integral for the Young topology on `R`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 251-252, PDF 262-263, Lemma 8.2.5 (corrected — `statements.jsonl`'s extraction cuts off after "Then")

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Bounding

open MeasureTheory ProbabilityTheory

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] [OpensMeasurableSpace U]

/-- Lemma 8.2.5 (Bäuerle–Rieder, p. 251-252, PDF 262-263). Let `b` be a continuous upper bounding
function and let (ii) and (iii) of the Continuity and Compactness Assumptions be satisfied (`R`
with the Young topology). Let `w : E × U → ℝ` be upper semicontinuous with `w(x,u) ≤ c_w b(x)`
for some `c_w > 0`. Then `(x,α) ↦ ∫_0^∞ e^{-(β+λ)t} [∫_U w(φ_t^α(x),u) α_t(du)] dt` is upper
semicontinuous on `E × R` (values in `[-∞,∞]`). -/
theorem lemma_8_2_5 (Mk : PDMDPModel E U) (b : E → ℝ) (hb_cont : Continuous b) (cr cQ cφ : ℝ)
    (hbound : IsUpperBoundingFunctionPDMDP Mk b cr cQ cφ)
    (hii : letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
      ContinuousOn (fun p : ℝ × (ℝ → ProbabilityMeasure U) × E => Mk.φRel p.1 p.2.1 p.2.2)
        {p | 0 ≤ p.1})
    (hiii : letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
      Continuous (fun p : E × (ℝ → ProbabilityMeasure U) =>
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t p.2 p.1)))
    (w : E × U → ℝ) (hw_usc : UpperSemicontinuous w) (cw : ℝ) (hcw : 0 < cw)
    (hwle : ∀ x u, w (x, u) ≤ cw * b x) :
    letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
    UpperSemicontinuous fun p : E × (ℝ → ProbabilityMeasure U) =>
      erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
        ((Real.exp (-(Mk.β + Mk.lam) * t) : ℝ) : EReal) *
          erealIntegral (p.2 t).toMeasure fun u => ((w (Mk.φRel t p.2 p.1, u) : ℝ) : EReal) := by sorry

end MDPFinance.PDMDP
