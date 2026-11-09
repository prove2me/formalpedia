-- Prove2me | Theorems.Thm_MoranYanPAC_Main_private_pac_nearly_linear
-- name    : MoranYanPAC.Main.private_pac_nearly_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:58.269864+00:00
-- url     : https://prove2.me/theorems/63a0dda0-102e-447e-ba33-5eb26415aa7b
-- title:
--   Theorem 1 — nearly linear private PAC sample complexity
-- statement:
--   There is a positive universal constant $C$ such that, for every arbitrary domain $X$ and every nonempty binary class $H\subseteq\{0,1\}^X$ with Littlestone dimension $d\ge1$, the following holds. For $0<\alpha,\beta,\delta<1$ and $0<\varepsilon\le1$, a randomized learner $A$ can be chosen, depending on $H,d$ and these parameters but not on the unknown distribution or target, which is $(\varepsilon,\delta)$-differentially private on all finite input lists.
--
--   For every labeled probability distribution $P$ realizable almost surely by one fixed $h^*\in H$, under the source's ordinary measurable-loss and uniform-event convention, and every integer sample size
--
--   $$n\ge\left\lceil C\frac{d\log(d/(\alpha\varepsilon\delta))+\log(1/\beta)}{\alpha\varepsilon}\right\rceil,$$
--
--   the selected learner's experiment is well posed and satisfies
--
--   $$\Pr_{S\sim P^n,\,\hat h\sim A(S)}[L_P(\hat h)\le\alpha]\ge1-\beta.$$
--
--   The probability includes both sample and algorithm randomness. Outputs may lie outside $H$. Privacy includes unrealizable and empty inputs and sizes below the accuracy threshold. No computational-efficiency or properness assertion is included. The universal constant comes before every instance and parameter. The printed logarithm is retained, including the entire endpoint parameter regime; it is not replaced by $\log(ed/(\alpha\varepsilon\delta))$.
--
--   **Formalization Note.** The VC-event convention is explicit for the source's local universe $U$. The selected learner's measurable output losses and conditional-success integrand are conclusions, not assumptions supplied to evade an accuracy obligation. Countably supported output laws suffice because the source construction has finite support on each input; no support restriction is imposed on $P$ or on $H$.
--
--   Differences from the source:
--   - encoding: probabilities of the source randomized rules → normalized PMF laws and nonnegative iterated probabilities; reason: the source construction has finite support on each input; distributions on examples remain arbitrary
--   - encoding: the ordinary implicit measurability convention for learning probabilities → explicit individual-loss, one-sample and two-sample event measurability; well-posedness of the selected learner is asserted; reason: pins the events whose probabilities are used without assuming separability or making accuracy conditional on the chosen learner being measurable
--   - encoding: an asymptotic O bound on integer sample complexity → a positive universal real constant followed by a natural ceiling threshold and accuracy at every larger integer; reason: this spells out the full uniform mathematical content of O with exact integer rounding
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Theorem 1, p. 3 (PDF p. 3)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_MoranYanPAC_Main_PACExperiment

set_option autoImplicit false

open MeasureTheory

namespace MoranYanPAC.Main

/-- Theorem 1, p. 3. The constant precedes every instance. The learner is chosen
before the distribution and target, and is private at every size. The explicit
measurability predicates express the ordinary convention for the stated probabilities. -/
theorem private_pac_nearly_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (H : Set (X → Bool)) (d : ℕ), H.Nonempty →
      UnderstandingML.ldim H = d → 1 ≤ d →
      ∀ (α β ε δ : ℝ), 0 < α → α < 1 → 0 < β → β < 1 →
        0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
      ∃ A : List (X × Bool) → PMF (X → Bool), Private A ε δ ∧
        ∀ P : Measure (X × Bool), IsProbabilityMeasure P →
          VCEventsMeasurable (PrivLittlestone.localUniverse H d) P → Realizable H P →
          ∀ n : ℕ,
            ⌈C * ((d : ℝ) * Real.log ((d : ℝ) / (α * ε * δ)) +
              Real.log (1 / β)) / (α * ε)⌉₊ ≤ n →
            PACExperimentMeasurable A P α n ∧
            ENNReal.ofReal (1 - β) ≤ pacSuccessProbability A P α n := by sorry

end MoranYanPAC.Main
