-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_mesh_pointwise_certificates
-- name    : MasulloRH.unit_height_em_mesh_pointwise_certificates
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T17:34:15.254488+00:00
-- url     : https://prove2.me/theorems/3fb8113e-a0b8-4b38-a07d-237402c820c3
-- title:
--   Pointwise Euler–Maclaurin certificates on a unit-height rectangle mesh
-- statement:
--   Fix natural numbers $n$ and $k$. Put $d=1/(k+3)$, $L=100000+n$, $a=1/2+d$, $b=L+d$, and $M=16(100003+n)$. Show that there is a positive integer $m$ such that, at each sample
--   $$
--   s_{i,j}=a+(1-a)\frac{i}{m}+\mathrm{i}\left(b+(L+1-b)\frac{j}{m}\right),
--   \qquad 0\leq i,j\leq m,
--   $$
--   one can find positive integers $K$ and $N$ for which
--   $$
--   \frac{2M}{m}
--   + \frac{(100002+n+2K)^{2K+1}}{3\cdot 6^{2K} N^{2K}}
--   < \left|\operatorname{emFinite}(K,s_{i,j},N)\right|.
--   $$
--   The mesh size $m$ is shared across the rectangle. The order $K$ and cutoff $N$ may be chosen independently at each sample, so an evaluator can certify each sample at its own precision.
-- source:
--   Pointwise-precision form of MasulloRH.unit_height_em_mesh_certificates, https://prove2.me/theorems/40cad239-2efb-4a93-96c2-b10b55fc4a8a, using the verified uniform enclosure https://prove2.me/theorems/1e043161-8bba-425f-ba0d-2ddcb47971fe to recover a shared truncation.

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

theorem MasulloRH.unit_height_em_mesh_pointwise_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ m : ℕ, 0 < m ∧
      ∀ i j : Fin (m + 1), ∃ (K N : ℕ), 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by sorry
