-- Prove2me | Theorems.Thm_HunterPDE_Compactness_boundedMap_vanishes_on_memW0
-- name    : HunterPDE.Compactness.boundedMap_vanishes_on_memW0
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:31:25.378685+00:00
-- url     : https://prove2.me/theorems/6bb80312-9619-4104-b01a-accd986a088e
-- title:
--   A bounded map annihilating test functions vanishes on their Sobolev closure
-- statement:
--   Let $k,n,d$ be arbitrary nonnegative integers, $1\le p\le\infty$, and $\Omega\subseteq\mathbb R^n$. Let $T$ map real functions on $\mathbb R^n$ to real functions on $\mathbb R^d$. Suppose that $T$ preserves subtraction up to almost-everywhere equality on $W^{k,p}(\Omega)$, is bounded into $L^p$ by a finite constant $C$ times the Sobolev norm, and annihilates every smooth test function supported compactly inside $\Omega$. Then $Tf=0$ almost everywhere for every $f\in W^{k,p}_0(\Omega)$. No openness or boundary regularity of $\Omega$ is needed. The proof first verifies Sobolev membership of the approximants and their differences, then applies the bound at arbitrarily small approximation error. This generalizes the forward kernel inclusion in Hunter Theorem 3.44.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73.

import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Data.ENNReal.Inv

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.boundedMap_vanishes_on_memW0 {n k d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (C : ℝ≥0)
    (hsub : ∀ f g, MemW k p Ω f → MemW k p Ω g →
      T (f - g) =ᵐ[volume] T f - T g)
    (hbound : ∀ f, MemW k p Ω f → MemLp (T f) p volume ∧
      eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm k p Ω f)
    (hzero : ∀ φ, HunterPDE.Shared.IsTestFunction Ω φ → T φ =ᵐ[volume] 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW0 k p Ω f) :
    T f =ᵐ[volume] 0 := by sorry
