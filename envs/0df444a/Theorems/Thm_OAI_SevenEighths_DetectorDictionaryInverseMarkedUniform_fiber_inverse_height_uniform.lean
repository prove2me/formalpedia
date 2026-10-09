-- Prove2me | Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedUniform_fiber_inverse_height_uniform
-- name    : OAI.SevenEighths.DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:28.657879+00:00
-- url     : https://prove2.me/theorems/c10413c0-e3da-409c-bbf5-60edf7c22438
-- title:
--   Uniform height control for inverse fiber polynomials
-- statement:
--   For every $J\in\mathbb N$ there are $K\in\mathbb N$ and $C>0$ such that for every `Fiber` $F$ (over any $M,H$, label and slot types and parameters), every finite set `selected` of slots, $U>0$ and $E\ge0$: if for all $v$, $\sum_{u\in F.\mathrm{rows}}\|\texttt{polynomial}(F.\mathrm{family}\,u\,F.\mathrm{label})\,\mathrm{true}\,(\texttt{childLogTest referenceWindow}\,v)\,U^{F.r}\,0\,0\cdot F.\texttt{physicalProduct}\,\mathrm{selected}\,u\|^2\le E(1+|v|)^{2J}$, then for $n\le2$, $\sigma\in[0,1]$, `height` $\ge0$ and $t\in[-\mathrm{height},\mathrm{height}]$, the same sum with the profile $\texttt{logProfile}^{[n]}(F.\texttt{inverseProfile})$ at $\sigma$, $t$ is at most $C\,E(1+\mathrm{height})^K$.
--
--   Lean: `OAI.SevenEighths.DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform` in `lean/OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedUniform.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.DetectorDictionaryInverseMarkedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeDetectorRawFiber

theorem fiber_inverse_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+height)^K := by
  sorry

end SevenEighths.DetectorDictionaryInverseMarkedUniform

end

end OAI
end
