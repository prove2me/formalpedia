-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_mesh_certificates
-- name    : MasulloRH.unit_height_em_mesh_certificates
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:49:41.187799+00:00
-- url     : https://prove2.me/theorems/40cad239-2efb-4a93-96c2-b10b55fc4a8a
-- title:
--   Unit-height right-rectangle grid certificates for the Euler–Maclaurin approximant
-- statement:
--   For natural numbers $n, k$, set $d = \frac{1}{k+3}$, $L = 100000 + n$, $\mathrm{left} = \frac{1}{2} + d$, $\mathrm{bottom} = L + d$, $\mathrm{top} = L + 1$, and $M = 16(100003 + n)$. There exist positive integers $m, K, N$ such that, setting
--
--   $$
--   \mathrm{err}_{n,K,N} = \frac{(100002 + n + 2K)^{2K+1}}{3 \cdot 6^{2K} \cdot N^{2K}} \in \mathbb{Q},
--   $$
--
--   at every grid point $s_{i,j} = \left(\mathrm{left} + (1 - \mathrm{left})\frac{i}{m},\; \mathrm{bottom} + (\mathrm{top} - \mathrm{bottom})\frac{j}{m}\right)$ ($0 \le i, j \le m$), the finite Euler–Maclaurin approximant `ZetaReflection.EMHigh.emFinite K s N` satisfies
--
--   $$
--   \frac{2M}{m} + \mathrm{err}_{n,K,N} < \left|Z_{K,N}(s_{i,j})\right|.
--   $$
--
--   This isolates the finite-sum evaluation problem from the analytic continuation and derivative estimates of $\zeta(s)$: together with the proved derivative bound $M$ and the proved Euler–Maclaurin enclosure $\mathrm{err}_{n,K,N}$, it implies the full unit-height rectangle mesh certificate for $\zeta(s)$.
--
--   **Formalization Note.** Only the finite Dirichlet–Bernoulli approximant `ZetaReflection.EMHigh.emFinite` appears in the conclusion; neither `riemannZeta` nor `deriv riemannZeta` is referenced.
-- source:
--   Euler-Maclaurin finite-sum reduction of MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates (https://prove2.me/theorems/f9f6d44b-a148-4b98-8aa0-a911a4eaa8b4) via MasulloRH.unit_height_zeta_right_rectangle_deriv_bound (https://prove2.me/theorems/724f2f12-f6c3-4346-91a0-da366324b4c2) and MasulloRH.unit_height_em_enclosure (https://prove2.me/theorems/1e043161-8bba-425f-ba0d-2ddcb47971fe), responding to https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-ad8fb92e-0c03-4bee-937c-638f829135a3 .

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

theorem MasulloRH.unit_height_em_mesh_certificates (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    let M : ℚ := 16 * (100003 + n)
    ∃ (m K N : ℕ), 0 < m ∧ 1 ≤ K ∧ 1 ≤ N ∧
      let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
        (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
      ∀ i j : Fin (m + 1),
        let s : ℂ :=
          ⟨left + (1 - left) * ((i.val : ℝ) / m),
            bottom + (top - bottom) * ((j.val : ℝ) / m)⟩
        ((2 * M / m + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K s N‖ := by sorry
