-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_auxiliary_upper
-- name    : OAI.ShortEgyptian.auxiliary_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:26:19.590439+00:00
-- url     : https://prove2.me/theorems/6e33e494-46e0-47c1-ac16-07c654ab1af6
-- title:
--   Upper bound $M\le e^{204204S}$ for the auxiliary common denominator
-- statement:
--   Let $J$ be a finite set, $A$ an arbitrary set, $a\in\mathbb{N}$, $p_0:J\to\mathbb{N}$ and $p:A\to\mathbb{N}$, and let $f_0,\dots,f_{999}:J\times\{0,1\}\to A$ be $1000$ maps. The *auxiliary denominator* of these data is
--
--   $$M=2^a\prod_{j\in J}p_0(j)\prod_{i=0}^{999}\prod_{j\in J}p\big(f_i(j,0)\big)\,p\big(f_i(j,1)\big).$$
--
--   Let $D_M=2002\cdot102=204204$.
--
--   **Theorem.** Let $S$ be a real number with $S\ge2$ and $\log S>0$. Assume $|J|\le S/\log S$, $p_0(j)\le2S^{100}$ for every $j\in J$, $p(x)\le2S^{100}$ for every $x\in A$, and $2^a\le e^S$. Then
--
--   $$M\le e^{D_MS}.$$
--
--   The number $M$ is designed as a common denominator: it is divisible by $2^a$, by every product of a subset of the numbers $p_0(j)$, and by every product $\prod_{j\in J}p(f_i(j,I_j))$ with $I\in\{0,1\}^J$. The theorem shows that it is at most a fixed power of $e^S$, which is the upper half of the size requirement $e^S<M\le e^{D_MS}$ placed on the common denominator in the construction of short Egyptian fraction expansions.
--
--   **Formalization Note** $M$ is `auxiliaryDenominator a p₀ p f` with `f : Fin 1000 → (J × Bool) → A`, the second coordinates $0,1$ being `false`, `true`. The constant $D_M$ is `dimM`, defined as `(2*1000+2)*(100+2)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean#L63-L92

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

theorem OAI.ShortEgyptian.auxiliary_upper {J : Type uJ} {A : Type uA} [Fintype J]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : Fin 1000 → (J × Bool) → A)
    (hS : 2 ≤ S) (hlog : 0 < Real.log S) (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (h₀ : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (ha : (2:ℝ)^a ≤ Real.exp S) :
    (auxiliaryDenominator a p₀ p f:ℝ) ≤ Real.exp ((dimM:ℝ)*S) := by sorry
