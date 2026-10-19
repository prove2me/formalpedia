-- Prove2me | Theorems.Thm_OAI_ClassicalON_continuousFKG_pi
-- name    : OAI.ClassicalON.continuousFKG_pi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:51:20.313454+00:00
-- url     : https://prove2.me/theorems/e97f4602-0c03-4106-8b2a-24111b6cf554
-- title:
--   Continuous FKG (Harris) inequality for a finite product of a probability measure on a compact totally ordered space
-- statement:
--   Let $A$ be a totally ordered set with a compact, locally compact, second-countable topology and its Borel σ-algebra (`LinearOrder A`, `TopologicalSpace A`, `CompactSpace A`, `MeasurableSpace A`, `BorelSpace A`, `SecondCountableTopology A`, `LocallyCompactSpace A`), and let $\mu$ be a probability measure on $A$. Let $\iota$ be a finite type and give $A^\iota$ the coordinatewise lattice order and the product measure $\mu^{\otimes\iota}$ (`Measure.pi (fun _ : ι => μ)`). Then $\mu^{\otimes\iota}$ has the continuous FKG property (`ContinuousFKG`, from the definitions bundle of this split):
--
--   for every continuous, strictly positive, log-supermodular weight $w : A^\iota \to \mathbb R$, that is, $w(x)\,w(y) \le w(x \wedge y)\,w(x \vee y)$ for all $x, y$ (`LogSupermodular`), and for all continuous, nonnegative, monotone $f, g : A^\iota \to \mathbb R$,
--   $$\langle f\rangle_w\,\langle g\rangle_w \;\le\; \langle fg\rangle_w, \qquad \langle f\rangle_w = \frac{\int w f\,d\mu^{\otimes\iota}}{\int w\,d\mu^{\otimes\iota}}$$
--   (`ContinuousAssociated` with `weightedMean`).
--
--   Lean: `OAI.ClassicalON.continuousFKG_pi`.
-- source:
--   Classical (T. E. Harris, A lower bound for the critical probability in a certain percolation process, Proc. Cambridge Philos. Soc. 56 (1960), 13–20; C. M. Fortuin, P. W. Kasteleyn and J. Ginibre, Correlation inequalities on some partially ordered sets, Comm. Math. Phys. 22 (1971), 89–103). Proof: OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON/FinFKG.lean (OpenAI's theorem OAI.ClassicalON.continuousFKG_pi)

import Mathlib
import Definitions.Def_OAIQWCO000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uX uY uι

noncomputable section
open MeasureTheory
namespace ClassicalON

section Finite
variable {A : Type uA} [LinearOrder A] [TopologicalSpace A] [CompactSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [LocallyCompactSpace A] (μ : Measure A) [IsProbabilityMeasure μ]

theorem continuousFKG_pi {ι : Type uι} [Fintype ι] :
    ContinuousFKG (Measure.pi (fun _ : ι => μ)) := by
  sorry

end Finite
end ClassicalON

end

end OAI
end
