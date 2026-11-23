-- Prove2me | Theorems.Thm_NoHair_asymptotic_static_cartesian_ricci_expansion
-- name    : NoHair.asymptotic_static_cartesian_ricci_expansion
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T08:21:27.584825+00:00
-- url     : https://prove2.me/theorems/6209a466-4be1-4315-8a25-ebf2c6620dee
-- title:
--   Ricci expansion of a general asymptotically flat static metric
-- statement:
--   For a time-independent block metric $g=-N^2dt^2+h$, assume $N-1$ and $h-\delta$ decay as $r^{-1}$ with corresponding decay through two spatial derivatives. Then $\mathrm{Ric}_{00}(g)=\Delta_\delta N+O(r^{-4})$ and $\mathrm{Ric}_{ij}(g)=\mathrm{Ric}'_\delta(h)_{ij}-\partial_i\partial_j N+O(r^{-4})$. The bounds are uniform on the coordinate tail and do not require any field equation. They apply to metrics with arbitrary angular dependence.
-- source:
--   P. Miao and L.-F. Tam, Evaluation of the ADM mass and center of mass via the Ricci tensor, Proc. Amer. Math. Soc. 144 (2016), pp. 753–761, Theorem 1.1(a) and the Euclidean integration-by-parts identity in the proof of Theorem 2.1, equations (2.2)–(2.8), https://arxiv.org/abs/1408.3893, https://doi.org/10.1090/proc12726. For the time and spatial Ricci equations, see equations (5.4) and (5.5) of P. T. Chruściel, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf.

import Definitions.Def_NoHair_staticCartesianRicci

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.asymptotic_static_cartesian_ricci_expansion (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∃ B : ℝ, ∀ x : ADMPoint, B < ‖x‖ → ContDiffAt ℝ ∞ N x ∧
      (∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) ∧ (∀ i j, h x i j = h x j i))
    (hd : ∀ k : ℕ, k ≤ 2 → ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
      ‖iteratedFDeriv ℝ k (fun y => N y - 1) x‖ ≤ C / ‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(k+1)) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
      |ricci (staticCartesianBlock N h) (staticTimeZero x) 0 0 - flatLapseLaplacian N x| ≤ C / ‖x‖^4 ∧
      ∀ i j : Fin 3, |ricci (staticCartesianBlock N h) (staticTimeZero x) i.succ j.succ -
        staticPrincipalRicci N h i j x| ≤ C / ‖x‖^4 := by sorry
