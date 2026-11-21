-- Prove2me | Theorems.Thm_MasulloAudit_monotone_cutoff_reversed_projection_trace
-- name    : MasulloAudit.monotone_cutoff_reversed_projection_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:55:41.799785+00:00
-- url     : https://prove2.me/theorems/1d9e5ed5-fb7f-47e5-bbe5-5b4562049d3b
-- title:
--   Nested finite coordinate cutoffs can retain a half-unit trace after reversing a projection
-- statement:
--   On the orthogonal sum H=ℓ²(ℕ,ℂ)⊕ℓ²(ℕ,ℂ) there exist an orthogonal projection P and a bounded operator A with PA=0 and AP=A. Let M_n keep coordinates 0 through n in the first copy and 0 through n−1 in the second. These nested finite-rank orthogonal multiplication cutoffs tend strongly to the identity. Each M_n AP is nuclear and its trace equals 1/2.
--
--   This isolates a limit issue when passing from the order P A in Theorem 10.4.2.2 to A P in Theorem 10.4.2.8. Even zero trace-class P A and strong convergence of monotone self-adjoint cutoffs do not force the cutoff traces of A P to approach zero. The theorem tests the general operator inference. The particular adelic convolution and projection in Chapter 10 may satisfy additional estimates.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 10.4.2.2, eq. (10.4.2.9), pp. 459–461, and Theorem 10.4.2.8, eqs. (10.4.2.20) and (10.4.2.34), pp. 463–464. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Filter Topology MasulloGRH

theorem MasulloAudit.monotone_cutoff_reversed_projection_trace :
    let L := lp (fun _ : ℕ => ℂ) 2
    let H := WithLp 2 (L × L)
    ∃ (P A : H →L[ℂ] H) (M : ℕ → H →L[ℂ] H), P.comp P=P ∧ IsSelfAdjoint P ∧
      P.comp A=0 ∧ A.comp P=A ∧
      (∀ n (u : H) j, (M n u).fst j = (if j<n+1 then u.fst j else 0) ∧
        (M n u).snd j = (if j<n then u.snd j else 0)) ∧
      (∀ u, Tendsto (fun n => M n u) atTop (𝓝 u)) ∧
      (∀ n, IsNuclearOperator ((M n).comp (A.comp P)) ∧ operatorTrace ((M n).comp (A.comp P)) = 1/2) := by sorry
