-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_backwards_recurrence_bound
-- name    : OAI.ShortEgyptian.backwards_recurrence_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:43:02.09034+00:00
-- url     : https://prove2.me/theorems/cf1e2cc6-f981-4210-ac7f-5089dd1ea6fd
-- title:
--   Unrolling the recurrence $f_j\le e^{-b}+e^{c}f_{j+1}^{\alpha}$ backwards from $f_d=0$
-- statement:
--   Let $f:\mathbb N\to\mathbb R$ be a sequence, let $d\in\mathbb N$, and let $\alpha,c,\gamma,b$ be real numbers with $0<\alpha\le1$, $\gamma\ge0$, $b\ge0$ and $c+\gamma\alpha=\gamma$. Assume that $f(j)\ge0$ for all $j$, that $f(d)=0$, and that for every $j<d$
--
--   $$
--   f(j)\le e^{-b}+e^{c}\,f(j+1)^{\alpha}.
--   $$
--
--   Then
--
--   $$
--   f(0)\le d\,\exp\big(\gamma-b\,\alpha^{d}\big).
--   $$
--
--   Taking logarithms, the multiplicative part of the recurrence acts as $x\mapsto c+\alpha x$, and the condition $c+\gamma\alpha=\gamma$ says that $\gamma$ is its fixed point; the additive error $e^{-b}$ is damped by the factor $\alpha^{d}$ after $d$ backward steps. The lemma propagates a terminal condition $f(d)=0$ back to the first index for sequences, such as densities of bad sets, that obey a sublinear one-step recurrence.
--
--   **Formalization Note** The power $f(j+1)^{\alpha}$ is the real power `Real.rpow`, applied to a nonnegative base, and $d$ is cast to a real number in the conclusion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/RecurrenceUnrolling.lean#L17-L50

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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence

open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.backwards_recurrence_bound (f : ℕ → ℝ) (d : ℕ) (α c γ b : ℝ)
    (ha : 0 < α) (ha' : α ≤ 1) (hg : 0 ≤ γ) (hb : 0 ≤ b)
    (hfix : c+γ*α=γ) (hf : ∀ j, 0 ≤ f j) (hend : f d=0)
    (hrec : ∀ j, j < d → f j ≤ Real.exp (-b)+Real.exp c*(f (j+1))^α) :
    f 0 ≤ (d:ℝ)*Real.exp (γ-b*α^d) := by sorry
