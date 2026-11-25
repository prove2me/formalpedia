-- Prove2me | Theorems.Thm_MaxPointDerivatives
-- name    : MaxPointDerivatives
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:50:24.356043+00:00
-- url     : https://prove2.me/theorems/067fd938-48ba-4e01-a9c0-e325289cd938
-- title:
--   Max Point Derivatives: Max Point Derivatives
-- statement:
--   At a normalized maximum point `e` of a homogeneous polynomial on the unit
--   sphere: `grad u e = m • e` and `D²u(e)[e,e] = m(m-1)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MaxPointDerivatives.lean#L13-L141
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/MaxPointDerivatives.lean#L13-L141

module
public import Definitions.Def_PHarmonicPoly_GradientEuler
public import Definitions.Def_PHarmonicPoly_MvPolyFDeriv
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_MaxPointDerivatives
public import Theorems.Thm_GradientEuler
public import Theorems.Thm_MvPolyFDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem MaxPointDerivatives {n m : ℕ} (hm : 1 ≤ m) {P : MvPolynomial (Fin n) ℝ}
    (hhom : P.IsHomogeneous m)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1) :
    gradient (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
        = (m : ℝ) • e
      ∧ iteratedFDeriv ℝ 2
          (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![e, e]
        = (m : ℝ) * ((m : ℝ) - 1) := by sorry
