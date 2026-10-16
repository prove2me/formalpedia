-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_auxiliary_lower
-- name    : OAI.ShortEgyptian.auxiliary_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:28:27.34471+00:00
-- url     : https://prove2.me/theorems/6e36337a-1b84-491b-b7f9-04e8bc7ba6fa
-- title:
--   The auxiliary common denominator exceeds $e^S$
-- statement:
--   Let $J$ and $R$ be finite sets, $A$ an arbitrary set, $a\in\mathbb{N}$, $p_0:J\to\mathbb{N}$ and $p:A\to\mathbb{N}$, and for each $i\in R$ let $f_i:J\times\{0,1\}\to A$. The *auxiliary denominator* of these data is
--
--   $$M=2^a\prod_{j\in J}p_0(j)\prod_{i\in R}\prod_{j\in J}p\big(f_i(j,0)\big)\,p\big(f_i(j,1)\big).$$
--
--   **Theorem.** Let $S>0$ be a real number with $\log S>0$. Assume $|J|\ge S/(2\log S)$, that $p_0(j)\ge S^{100}$ and $p_0(j)>0$ for every $j\in J$, and that $p(x)>0$ for every $x\in A$. Then
--
--   $$e^S<M.$$
--
--   Together with the companion upper bound $M\le e^{204204S}$ (for $|R|=1000$ and suitably bounded primes), this gives the size condition $e^S<M\le e^{204204S}$ on the common denominator in the construction of short Egyptian fraction expansions. The lower bound guarantees, for example, that every numerator $u\le e^S$ is smaller than $M$, so that $u/M<1$.
--
--   **Formalization Note** $M$ is `auxiliaryDenominator a p₀ p f`, the index set $R$ is an arbitrary finite type, and the second coordinate $0,1$ is `Bool`. The hypothesis $p_0(j)>0$ already follows from $p_0(j)\ge S^{100}$ and $S>0$, but is stated separately in Lean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean#L94-L114

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds

open OAI OAI.ShortEgyptian
universe uJ uA uR
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology

theorem OAI.ShortEgyptian.auxiliary_lower {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A)
    (hS : 0 < S) (hlog : 0 < Real.log S) (hm : S/(2*Real.log S) ≤ (Fintype.card J:ℝ))
    (h₀ : ∀ j, S^100 ≤ (p₀ j:ℝ)) (h₀pos : ∀ j, 0 < p₀ j) (hp : ∀ x, 0 < p x) :
    Real.exp S < (auxiliaryDenominator a p₀ p f:ℝ) := by sorry
