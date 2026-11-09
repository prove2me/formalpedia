-- Prove2me | Theorems.Thm_MoranYanPAC_Main_vc_generalization
-- name    : MoranYanPAC.Main.vc_generalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:41.381206+00:00
-- url     : https://prove2.me/theorems/55daeb8b-8fb2-45cc-9778-5e8db5a15485
-- title:
--   Lemma 1 — relative VC generalization
-- statement:
--   There is a positive universal constant $C_{\rm VC}$ with the following property. Let $G$ be a binary class on an arbitrary domain with $\operatorname{VCdim}(G)\le d$, where $d\ge1$. Let $0<\alpha,\beta<1$, and let $P$ be any probability distribution on labeled examples, with the ordinary measurable-loss and uniform-event convention made explicit. If
--
--   $$n\ge C_{\rm VC}\frac{d\log(e/\alpha)+\log(1/\beta)}{\alpha},$$
--
--   then, with probability at least $1-\beta$ over $S\sim P^n$, simultaneously every $h\in G$ satisfies
--
--   $$\ell_S(h)/n\le\alpha/2\quad\Longrightarrow\quad L_P(h)\le\alpha.$$
--
--   Realizability is not required. The constant precedes the domain, class, dimension, distribution, parameters and sample size. This is the relative generalization rate needed for the headline's $1/\alpha$ dependence, rather than a consistent-only or absolute-error bound. Individual loss events and both the one-sample bad events and two-sample comparison events are required measurable; no separable subclass is assumed.
--
--   Differences from the source:
--   - encoding: ordinary measurable-event convention for VC probabilities → the explicit VCEventsMeasurable event list; reason: makes the probabilities well posed without countability or pointwise separability
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 1, p. 15 (PDF p. 15)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MoranYanPAC_Main_PACExperiment

set_option autoImplicit false

open MeasureTheory

namespace MoranYanPAC.Main

/-- Lemma 1, p. 15. One universal constant, all labeled distributions,
and a simultaneous conclusion including empirical error up to α/2. -/
theorem vc_generalization :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (G : Set (X → Bool)) (d : ℕ), 1 ≤ d → UnderstandingML.vcDim G ≤ d →
      ∀ (α β : ℝ), 0 < α → α < 1 → 0 < β → β < 1 →
      ∀ (P : Measure (X × Bool)), IsProbabilityMeasure P → VCEventsMeasurable G P →
      ∀ n : ℕ,
        C * ((d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / β)) / α ≤ n →
        ENNReal.ofReal (1 - β) ≤ sampleLaw P n (vcSuccessEvent G P α n) := by sorry

end MoranYanPAC.Main
