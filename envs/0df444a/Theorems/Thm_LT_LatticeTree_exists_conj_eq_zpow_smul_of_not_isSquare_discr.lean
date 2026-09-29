-- Prove2me | Theorems.Thm_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
-- name    : LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/f98cf6e7-e1b5-564c-acb9-0b39f9b84778
-- title:
--   Normal forms for elliptic conjugacy classes in GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers, $K_v$ the $v$-adic completion and $\mathcal{O}_v$ its valuation ring; let $\varpi \in \mathcal{O}_v$ be irreducible, and let $\gamma \in \mathrm{GL}_2(K_v)$ be such that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is not a square in $K_v$. Then there are $x \in \mathrm{GL}_2(K_v)$ and $k \in \mathbb{Z}$ for which $x^{-1}\gamma x$ takes one of three forms, in each case $\varpi^{k}$ times the image in $M_2(K_v)$ of an integral matrix. First: $x^{-1}\gamma x = \varpi^{k}\gamma'$ with $\gamma' \in \mathrm{GL}_2(\mathcal{O}_v)$ of the shape $\gamma' = \mu\cdot 1 + \varpi^{d} Y$ entrywise, for some $d \in \mathbb{N}$, a unit $\mu \in \mathcal{O}_v^\times$ and $Y \in M_2(\mathcal{O}_v)$ whose reduction modulo the ideal $(\varpi)$ has no eigenvector: for every $a$ and every vector $w$ over $\mathcal{O}_v/(\varpi)$, if $\bar Y w = a w$ then $w = 0$. Second: the same shape $\gamma' = \mu\cdot 1 + \varpi^{d}Y$ with $\gamma' \in \mathrm{GL}_2(\mathcal{O}_v)$, where now $Y_{00}Y_{11} - Y_{01}Y_{10} = \varpi w$ for some unit $w$ and $\varpi \mid Y_{00} + Y_{11}$. Third: $x^{-1}\gamma x = \varpi^{k} Y$ with $Y \in M_2(\mathcal{O}_v)$ satisfying $Y_{00}Y_{11} - Y_{01}Y_{10} = \varpi w$ for a unit $w$ and $\varpi \mid Y_{00} + Y_{11}$.
--
--   This is the local normal form for an elliptic (irreducible characteristic polynomial) element of $\mathrm{GL}_2$ over a non-archimedean completion of a number field, the three cases corresponding to the unramified case, the ramified case with integral scaling, and the ramified case with an Eisenstein matrix. It is used in the computation of local orbital integrals and in the construction of matching Hecke operators at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix
open NumberField IsDedekindDomain

theorem LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) :
    ∃ (x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) (k : ℤ),
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        (∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})
            (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}),
          (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) :
              v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
          (w : (v.adicCompletionIntegers K)ˣ),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) (w : (v.adicCompletionIntegers K)ˣ),
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            Y.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              : v.adicCompletionIntegers K → v.adicCompletion K)) := by sorry
