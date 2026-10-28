-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_FreeCornerPosition_symmetry_bound
-- name    : OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:54:51.138046+00:00
-- url     : https://prove2.me/theorems/e711e6ed-f422-4850-9863-9b3ae2c2295b
-- title:
--   OAI.Kadison.TracialSequence.FreeCornerPosition.symmetry_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator`, `open Filter`, `open FreeMoments`):
--
--   ```lean
--   theorem FreeCornerPosition.symmetry_bound (F : FreeCornerPosition τ ω Q j)
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop) (hone : τ 1=1)
--       (T : τ.GNS →L[ℂ] τ.GNS)
--       (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
--       {b c β : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β ≤ 1) (hβb : β<b)
--       (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re ≤ b →
--         ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
--       (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
--       ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖ ≤ 1040*c
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.TracialSequence.FreeCornerPosition` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067

section

attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FreeMoments

variable {A K : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)

theorem FreeCornerPosition.symmetry_bound (F : FreeCornerPosition τ ω Q j)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop) (hone : τ 1=1)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β ≤ 1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re ≤ b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖ ≤ 1040*c := by
  sorry

end Kadison.TracialSequence

end

end OAI
end
