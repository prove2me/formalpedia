-- Prove2me | Theorems.Thm_MTT_Cohomology_integral_class_character_law_infty
-- name    : MTT.Cohomology.integral_class_character_law_infty
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T04:27:54.615721+00:00
-- url     : https://prove2.me/theorems/22efc626-cd61-4565-b6f0-544764368d75
-- title:
--   Nebentype law of the modular integral on paths from the cusp at infinity
-- statement:
--   Let f be a normalized algebraic cuspidal Hecke eigenform of level N and weight k, with nebentypus character epsilon, and let phi be a compactly supported cohomology class whose integral coefficient evaluations reproduce the modular integrals of f. Then for every matrix gamma in Gamma_0(N) the value of phi on the image under gamma of the path from the cusp at infinity to a rational cusp r transforms by epsilon(d) times the coefficient action of gamma, where d is the lower right entry of gamma.
--
--   This is the restriction of the full nebentypus law to paths issuing from the cusp at infinity, and it is the whole analytic content of that law: since a class satisfying the integral normalization has its value at such a path given explicitly by the period polynomial of f, the assertion is the classical transformation law of the period polynomial under Gamma_0(N). The extension from these paths to arbitrary pairs of cusps is formal, using only the cocycle relation.
--
--   A proof must relate the integral of f along the vertical ray above r to the integral along its image under gamma, which is a circular arc rather than a ray. This is a contour deformation, justified by holomorphy of f together with its decay at the cusps, and it is where the analytic work lies.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), §4

import Definitions.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_character_law_infty
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (r : ℚ) :
    φ.val (cuspAct γ.val OnePoint.infty, cuspAct γ.val ((r : ℚ) : Cusp))
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) •
          act γ.val.val (φ.val (OnePoint.infty, ((r : ℚ) : Cusp))) := by sorry
