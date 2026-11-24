-- Prove2me | Theorems.Thm_InvariantEKF_error_fields_homogeneous
-- name    : InvariantEKF.error_fields_homogeneous
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:17:25.274313+00:00
-- url     : https://prove2.me/theorems/3d448f20-933e-4630-b760-fcf8795d3a61
-- title:
--   Lemma 1: $g^R_u$ and $g^L_u$ satisfy $g_u(ab)=ag_u(b)+g_u(a)b$ and govern the invariant errors
-- statement:
--   Let $G$ be a matrix Lie group and let the system $\frac{d}{dt}\chi_t=f_{u_t}(\chi_t)$, $t\ge0$, be group affine: $f_u(ab)=af_u(b)+f_u(a)b-af_u(I)b$ for all inputs $u$ and $a,b\in G$. Then:
--
--   1. $g^R_u(\eta)=f_u(\eta)-\eta f_u(I)$ satisfies $g^R_u(ab)=a\,g^R_u(b)+g^R_u(a)\,b$ for all $a,b\in G$. For any two trajectories $\chi,\bar\chi$ one has $\chi_t=\eta^R_t\bar\chi_t$ with $\eta^R_t=\chi_t\bar\chi_t^{-1}$, and $\frac{d}{dt}\eta^R_t=g^R_{u_t}(\eta^R_t)$.
--   2. $g^L_u(\eta)=f_u(\eta)-f_u(I)\eta$ satisfies $g^L_u(ab)=a\,g^L_u(b)+g^L_u(a)\,b$ for all $a,b\in G$. For any two trajectories one has $\chi_t=\bar\chi_t\eta^L_t$ with $\eta^L_t=\bar\chi_t^{-1}\chi_t$, and $\frac{d}{dt}\eta^L_t=g^L_{u_t}(\eta^L_t)$.
--
--   **Formalization Note** "All the solutions have the form $\chi_t=\eta^R_t\bar\chi_t$" is stated as: for every solution $\chi$, the matrix $\eta^R_t=\chi_t\bar\chi_t^{-1}$ satisfies the error equation. Derivatives at $t=0$ are one-sided.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Appendix B, Lemma 1, eq. (57), p. 26

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem error_fields_homogeneous {N : ℕ} {U : Type*} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (hG : IsMatrixLieGroup G) (f : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hf : IsGroupAffine G f) (u : ℝ → U) :
    (∀ v, ∀ a ∈ G, ∀ b ∈ G,
      errField false f v (a * b) = a * errField false f v b + errField false f v a * b) ∧
    (∀ χ χbar : ℝ → Matrix (Fin N) (Fin N) ℝ,
      IsTrajectory G f u (Set.Ici 0) χ → IsTrajectory G f u (Set.Ici 0) χbar →
      ∀ t, 0 ≤ t → χ t = invError false (χbar t) (χ t) * χbar t ∧
        HasMatDerivWithinAt (fun s => invError false (χbar s) (χ s))
          (errField false f (u t) (invError false (χbar t) (χ t))) (Set.Ici 0) t) ∧
    (∀ v, ∀ a ∈ G, ∀ b ∈ G,
      errField true f v (a * b) = a * errField true f v b + errField true f v a * b) ∧
    (∀ χ χbar : ℝ → Matrix (Fin N) (Fin N) ℝ,
      IsTrajectory G f u (Set.Ici 0) χ → IsTrajectory G f u (Set.Ici 0) χbar →
      ∀ t, 0 ≤ t → χ t = χbar t * invError true (χbar t) (χ t) ∧
        HasMatDerivWithinAt (fun s => invError true (χbar s) (χ s))
          (errField true f (u t) (invError true (χbar t) (χ t))) (Set.Ici 0) t) := by sorry

end InvariantEKF
