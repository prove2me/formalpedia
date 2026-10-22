-- Prove2me | Theorems.Thm_JHolomorphic_contDiff_mul_of_tsupport_subset
-- name    : JHolomorphic.contDiff_mul_of_tsupport_subset
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:41:57.586797+00:00
-- url     : https://prove2.me/theorems/17469269-2b8c-4f84-b4ad-bbf994b792c2
-- title:
--   A function $C^n$ on $U$ times a $C^n$ function supported in $U$ is $C^n$ on $\mathbb{C}$
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open, $n\in\mathbb{N}\cup\{\infty\}$, let $\varphi:\mathbb{C}\to\mathbb{R}$ be $C^n$ with closed support contained in $U$, and let $a:\mathbb{C}\to\mathbb{R}$ be $C^n$ on $U$. Then $z\mapsto\varphi(z)\,a(z)$ is $C^n$ on all of $\mathbb{C}$.
--
--   **Formalization Note** $n$ is an `ℕ∞`; the hypotheses are `ContDiff ℝ n φ`, `tsupport φ ⊆ U`, `ContDiffOn ℝ n a U`.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- The product of a `Cⁿ` function with closed support in an open set `U` and a function that
is `Cⁿ` on `U` is `Cⁿ` on all of `ℂ`. -/
theorem contDiff_mul_of_tsupport_subset {U : Set ℂ} (hU : IsOpen U) {n : ℕ∞} {φ a : ℂ → ℝ}
    (hφ : ContDiff ℝ n φ) (hφU : tsupport φ ⊆ U) (ha : ContDiffOn ℝ n a U) :
    ContDiff ℝ n (fun z => φ z * a z) := by
  sorry

end JHolomorphic
