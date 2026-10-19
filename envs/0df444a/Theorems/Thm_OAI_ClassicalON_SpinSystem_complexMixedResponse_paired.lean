-- Prove2me | Theorems.Thm_OAI_ClassicalON_SpinSystem_complexMixedResponse_paired
-- name    : OAI.ClassicalON.SpinSystem.complexMixedResponse_paired
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:22.360041+00:00
-- url     : https://prove2.me/theorems/fa4278c0-ab70-43b1-b273-d8a73daf53fb
-- title:
--   A pairing identity for complex mixed responses of a pinned O(3) spin system (OpenAI classical O(n))
-- statement:
--   **Objects** (definitions bundle `OAIQWCO002` of this split). A `SpinSystem 3 V E` on finite types $V, E$ has edge endpoints `left`, `right`, couplings and pins `pin : V → Option (Spin 3)`. For $f : V \to \mathbb C$, `S.differential f e` $= f(\mathrm{right}\,e) - f(\mathrm{left}\,e)$, and `S.commutatorForm f g e` $= \tfrac12\bigl(f(\mathrm{left}\,e)\,g(\mathrm{right}\,e) - g(\mathrm{left}\,e)\,f(\mathrm{right}\,e)\bigr)$. `S.complexSecondResponse u v` and `S.complexMixedResponse u v w z` are the Gibbs averages (`averageComplexLinear`) of OpenAI's second-order and mixed fourth-order response observables `complexSecondObservable` and `complexMixedObservable` built from edge functions.
--
--   **Statement.** Let $S$ be such a spin system and $f, g : V \to \mathbb C$ vanish at every pinned vertex. Writing $\partial$ for `S.differential` and $[\cdot,\cdot]$ for `S.commutatorForm`,
--   $$\mathrm{complexMixedResponse}\bigl(\partial f,\ \overline{\partial f},\ \overline{\partial g},\ \partial g\bigr) \;=\; \mathrm{complexSecondResponse}\bigl([f, \bar f],\ \overline{[g, \bar g]}\bigr) - \mathrm{complexSecondResponse}\bigl([f, g],\ \overline{[f, g]}\bigr),$$
--   with complex conjugation applied edgewise.
--
--   Lean: `OAI.ClassicalON.SpinSystem.complexMixedResponse_paired`, OpenAI's theorem of that name.
-- source:
--   OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON/RotationInequality.lean (declaration OAI.ClassicalON.SpinSystem.complexMixedResponse_paired)

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype I] in
theorem complexMixedResponse_paired (S : SpinSystem 3 V E) (f g : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.complexMixedResponse (S.differential f) (fun e => conj (S.differential f e))
      (fun e => conj (S.differential g e)) (S.differential g) =
      S.complexSecondResponse (S.commutatorForm f (fun x => conj (f x)))
        (fun e => conj (S.commutatorForm g (fun x => conj (g x)) e)) -
      S.complexSecondResponse (S.commutatorForm f g) (fun e => conj (S.commutatorForm f g e)) := by
  sorry

end ClassicalON.SpinSystem

end

end OAI
end
