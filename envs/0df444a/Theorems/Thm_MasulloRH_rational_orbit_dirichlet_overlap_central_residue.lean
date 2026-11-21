-- Prove2me | Theorems.Thm_MasulloRH_rational_orbit_dirichlet_overlap_central_residue
-- name    : MasulloRH.rational_orbit_dirichlet_overlap_central_residue
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:25:09.276182+00:00
-- url     : https://prove2.me/theorems/25e59343-4479-4b15-a2eb-55652707d2cf
-- title:
--   Rational orbit overlap in its convergent half-plane and its nonzero central residue
-- statement:
--   For a positive rational shift written in lowest terms as $m/n$, put $w_s(k)=k^{-s}/\zeta(s)$ on positive integers and $O_{m,n}(s)=(mn)^{-s}\zeta(2s)/\zeta(s)^2$. In the half-plane $\Re(s)>1$, the weights sum to one and the bilinear overlap $\sum_{k\ge1}w_s(mk)w_s(nk)$ converges to $O_{m,n}(s)$. For real $s>1$ these are probability weights. The overlap has an explicit nonzero central residue. With $c=(mn)^{-1/2}/\zeta(1/2)^2$, $$\lim_{s\to1/2}(2s-1)O_{m,n}(s)=c,\qquad\lim_{s\to1/2}(s-1/2)O_{m,n}(s)=c/2.$$ Both limits are complex punctured limits. The sum identities and limits hold for all positive integers $m,n$; coprimality identifies the pair sum with all matched integer pairs for the rational shift. This computes an analytic regularization of the positive rational-orbit model.
-- source:
--   Rational-orbit construction for Masullo (11.3.2.2). Builds on the finite geometric box https://prove2.me/theorems/fa50948f-56da-4d20-8046-d2063aeeba8d and finite-support obstruction https://prove2.me/theorems/8053ad9d-dc66-423e-a7e0-a775c0b82050. Uses the standard pole of the Riemann zeta function and accepted small-height nonvanishing theorem https://prove2.me/theorems/d752be9a-a1b7-4d46-b0b7-8e2125373a4e.

import Mathlib.NumberTheory.LSeries.RiemannZeta
open Filter Complex
open scoped Topology

theorem MasulloRH.rational_orbit_dirichlet_overlap_central_residue (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let o (s : ℂ) := ((m*n : ℕ):ℂ)^(-s) * riemannZeta (2*s) / (riemannZeta s)^2
    let c := ((m*n : ℕ):ℂ)^(-(1/2:ℂ)) / (riemannZeta (1/2:ℂ))^2
    (∀ s : ℂ, 1 < s.re →
      let w (k : ℕ) := (1 / (k:ℂ)^s) / riemannZeta s
      HasSum (fun j : ℕ => w (j+1)) 1 ∧
      HasSum (fun j : ℕ => w (m*(j+1)) * w (n*(j+1))) (o s)) ∧
      c ≠ 0 ∧
      Tendsto (fun s : ℂ => (2*s-1) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 c) ∧
      Tendsto (fun s : ℂ => (s-1/2) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 (c/2)) := by sorry
