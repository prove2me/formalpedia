-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_adaptive_ball_certificates
-- name    : MasulloRH.unit_height_em_adaptive_ball_certificates
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T18:09:28.578883+00:00
-- url     : https://prove2.me/theorems/fa0bbf43-2258-465f-95d2-56813214d210
-- title:
--   Adaptive Euler–Maclaurin ball certificates for unit-height rectangles
-- statement:
--   For each of the target unit-height rectangles $R_{n,k}$, find a finite set of centers with rational real and imaginary coordinates in $R_{n,k}$. Assign a rational radius $r_p$ and positive Euler–Maclaurin parameters $K_p,N_p$ to each center $p$. Require that the open balls cover $R_{n,k}$, and certify
--   $$
--   M_n r_p+\mathrm{err}_{n,K_p,N_p}<|\operatorname{emFinite}(K_p,p,N_p)|
--   $$
--   at every center, where $M_n=16(100003+n)$ and $\mathrm{err}$ is the unit-height enclosure radius. Both the radii and the evaluation precision can vary across the cover.
-- source:
--   Adaptive-cover version of https://prove2.me/theorems/3fb8113e-a0b8-4b38-a07d-237402c820c3, using the rectangle derivative bound https://prove2.me/theorems/724f2f12-f6c3-4346-91a0-da366324b4c2.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

open Set

theorem MasulloRH.unit_height_em_adaptive_ball_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    let R := Complex.reProdIm (Icc left 1) (Icc bottom top)
    let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
    ∃ (points : Finset (ℚ × ℚ)) (radius : ℚ × ℚ → ℚ),
      (∀ p ∈ points, center p ∈ R ∧ ∃ (K N : ℕ), 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        ((M * radius p + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (center p) N‖) ∧
      ∀ s ∈ R, ∃ p ∈ points, dist s (center p) < (radius p : ℝ) := by sorry
