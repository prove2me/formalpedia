-- Prove2me | Theorems.Thm_MasulloRH_bilateral_scattering_coefficients
-- name    : MasulloRH.bilateral_scattering_coefficients
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:06:49.200182+00:00
-- url     : https://prove2.me/theorems/034e9368-95e0-4502-b670-58bfdee4852c
-- title:
--   Bilateral scattering correlations, their first moments, and the rank-two half-line correction
-- statement:
--   For $0<r<1$ take the coefficients $b_{-1}=-r$, $b_j=(1-r^2)r^j$ for $j\ge0$, and $b_j=0$ for $j<-1$. These are the Laurent coefficients of $(1-rz^{-1})/(1-rz)$. For every integer lag $d$,
--   $$\sum_{j\in\mathbf Z}b_{j-d}b_j=1_{d=0},\qquad \sum_{j\in\mathbf Z}j\,b_{j-d}b_j=1_{d\ne0}r^{|d|}.$$
--   Both series are absolutely convergent. For every pair $i,j\in\mathbf Z$ the half-line entry sum converges absolutely and satisfies
--   $$\sum_{k\le0}b_{i-k}b_{j-k}-1_{i=j,\ i\le0}=(1-r^2)r^{i+j}1_{i,j\ge0}-1_{i=j=0}.$$
--   Thus the half-line correction has the entries of the difference of the rank-one projections onto $v_i=\sqrt{1-r^2}\,r^i1_{i\ge0}$ and onto the coordinate at zero. At a prime $p$, substituting $r=p^{-1/2}$ gives the positive off-diagonal coefficients $p^{-|d|/2}$.
-- source:
--   Discrete coefficient calculation for the unramified valuation-chart scattering model in the Masullo RH mission, Chapters 11–12. The shift convention is Dg(u)=g(u+L), with L=log p and r=p^(−1/2) in the local prime specialization.

import Mathlib.Analysis.SpecificLimits.Normed

theorem MasulloRH.bilateral_scattering_coefficients (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    let b (j : ℤ) := if j = -1 then -r else if 0 ≤ j then (1-r^2)*r^j.toNat else 0
    (∀ d : ℤ,
      HasSum (fun j : ℤ => b (j-d)*b j) (if d=0 then 1 else 0) ∧
      HasSum (fun j : ℤ => (j:ℝ)*b (j-d)*b j) (if d=0 then 0 else r^d.natAbs)) ∧
    (∀ i j : ℤ,
      let c (k : ℤ) := if k ≤ 0 then b (i-k)*b (j-k) else 0
      Summable c ∧
        (∑' k : ℤ, c k) - (if i=j ∧ i ≤ 0 then 1 else 0) =
          (if 0 ≤ i ∧ 0 ≤ j then (1-r^2)*r^(i.toNat+j.toNat) else 0) -
          (if i=0 ∧ j=0 then 1 else 0)) := by sorry
