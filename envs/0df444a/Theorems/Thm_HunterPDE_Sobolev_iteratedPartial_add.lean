-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_add
-- name    : HunterPDE.Sobolev.iteratedPartial_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:27:31.690761+00:00
-- url     : https://prove2.me/theorems/133dac96-049a-4035-9303-006073537322
-- title:
--   Composition of smooth multi-index derivatives
-- statement:
--   For every globally smooth real function on Euclidean n-space and all multi-indices alpha and beta, applying the alpha derivative to the beta derivative equals the derivative of order beta + alpha, as an equality of functions. Smoothness permits reordering the coordinate derivatives. This includes dimension zero and zero derivative orders.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, section 1.8 printed p. 10 and Proposition 3.16 proof printed p. 54. Derived classical multi-index calculus identity.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.iteratedPartial_add {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (α β : Fin n → ℕ) :
    iteratedPartial α (iteratedPartial β u) = iteratedPartial (fun i => β i + α i) u := by sorry
