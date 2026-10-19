-- Prove2me | Theorems.Thm_OAI_FiniteEntropySeparation_lowerSemicontinuous_freeFisher
-- name    : OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:01.216067+00:00
-- url     : https://prove2.me/theorems/bb62a550-30f0-4b6d-9e73-61985807beaf
-- title:
--   Lower semicontinuity of Voiculescu's free Fisher information along continuous families of operator tuples
-- statement:
--   Let $H$ be a complex Hilbert space (`NormedAddCommGroup H`, `InnerProductSpace ℂ H`, `CompleteSpace H`, $H$ in `Type`), $\langle\cdot,\cdot\rangle$ its inner product (linear in the second argument), and $M$ a von Neumann algebra on $H$ (`VonNeumannAlgebra H`).
--
--   Definitions used (all from the published bundle `Def_FiniteEntropySeparation`):
--   - A `TracialVector M` is a unit vector $\Omega \in H$ (`vacuum`) with $\langle \Omega, AB\,\Omega\rangle = \langle \Omega, BA\,\Omega\rangle$ for all $A, B \in M$, and such that $A\Omega = 0$ implies $A = 0$ for $A \in M$. Write $\tau(A) = \langle\Omega, A\Omega\rangle$ (`trace`).
--   - For $X = (X_1, \dots, X_n)$, a tuple of bounded operators on $H$ (`Fin n → H →L[ℂ] H`), and a word $w = (i_1, \dots, i_m)$ in $\{1, \dots, n\}$, `wordEval X w` is $X_{i_1}\cdots X_{i_m}$ and `wordMoment τ X w` is $\tau(X_{i_1}\cdots X_{i_m})$. `polynomialL2 τ X` is the closure of the span of the vectors $X_{i_1}\cdots X_{i_m}\Omega$.
--   - `derivativeMoment τ X i w` is $\sum_{r : w_r = i} \tau(\text{word before } r)\,\tau(\text{word after } r)$.
--   - $\xi = (\xi_1, \dots, \xi_n)$, $\xi_i \in H$, is a conjugate system for $X$ (`ConjugateSystem τ X ξ`) if every $\xi_i \in$ `polynomialL2 τ X` and $\langle \xi_i, X_{i_1}\cdots X_{i_m}\Omega\rangle = $ `derivativeMoment τ X i w` for every $i$ and every word $w$.
--   - The free Fisher information (`freeFisher τ X`, valued in $[0, \infty]$) is the infimum of $\sum_i \|\xi_i\|^2$ over conjugate systems $\xi$ (and $\infty$ if there is none).
--
--   Let $\tau$ be a `TracialVector M`, $T$ a topological space, $n \in \mathbb N$, and $X : T \to (\mathrm{Fin}\ n \to H \to_L H)$ such that $t \mapsto X(t)_i$ is continuous for every $i$, for the operator-norm topology. Assume that for every $t \in T$ the tuple $X(t)$ has a conjugate system. Then
--   $$t \;\longmapsto\; \mathrm{freeFisher}\ \tau\ (X(t)) \in [0, \infty]$$
--   is lower semicontinuous (`LowerSemicontinuous`).
--
--   Lean: `OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher`, OpenAI's theorem of that name (in `lean/OAI/Analysis/FreeEntropy/FisherVariational.lean`). All definitions in the statement come from the published bundle `Def_FiniteEntropySeparation`.
-- source:
--   D. Voiculescu, The analogues of entropy and of Fisher's information measure in free probability theory, V: Noncommutative Hilbert transforms, Inventiones Mathematicae 132 (1998), 189–227 (the free Fisher information Φ* and conjugate variables). Proof: OpenAI, A finite-entropy separation of microstates and nonmicrostates free entropy, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 298, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeEntropy/FisherVariational.lean (declaration OAI.FiniteEntropySeparation.lowerSemicontinuous_freeFisher)

import Mathlib
import Definitions.Def_FiniteEntropySeparation

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lowerSemicontinuous_freeFisher {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {T : Type u5} [TopologicalSpace T] {n : ℕ}
    (X : T → Fin n → H →L[ℂ] H) (hX : ∀ i, Continuous (fun t => X t i))
    (he : ∀ t, ∃ ξ, ConjugateSystem τ (X t) ξ) :
    LowerSemicontinuous (fun t => freeFisher τ (X t)) := by
  sorry

end FiniteEntropySeparation

end

end OAI
end
