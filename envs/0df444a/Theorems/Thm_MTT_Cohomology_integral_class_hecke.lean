-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_class_hecke
-- name    : MTT.Cohomology.integral_class_hecke
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T04:33:19.853841+00:00
-- url     : https://prove2.me/theorems/3b89e47d-4df3-4261-9c0b-3153ce757814
-- title:
--   Hecke equivariance of the period polynomials
-- statement:
--   Let f be a weight-k cusp form of level N and let g be its image under the classical prime Hecke operator at a prime l, with the normalization that includes U_l when l divides the level. If a compactly supported cohomology class is analytically normalized for f, and another is analytically normalized for g, then the second is the image of the first under the explicit cohomological prime Hecke operator, the sum over the l upper-triangular cosets together with the character-weighted diagonal term.
--
--   The statement is phrased for arbitrary classes carrying the two normalizations rather than for a chosen integration map, so it does not presuppose that such an integration map has been constructed, and it does not presuppose linearity. Since a class carrying a given analytic normalization is unique, the statement is equivalent to Hecke equivariance of the integration map, but it isolates the analytic identity: the modular integrals of the Hecke translate of f are the corresponding combination of modular integrals of f over the coset translates of the path.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), Theorem 2.3 and §4

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_hecke
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (e : DirichletCharacter ℂ N) (l : ℕ) (hl : l.Prime)
    (f g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ z, g z = MTT.heckePrime k (e l) l f z)
    (φ ψ : Hc N (k - 2) ℂ) (hφ : IntegralClass f φ) (hψ : IntegralClass g ψ) :
    ψ.val = primeHecke (e l) l φ.val := by sorry
