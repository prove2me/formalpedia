-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_enclosure
-- name    : MasulloRH.unit_height_em_enclosure
-- status  : Proved
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:48:14.648311+00:00
-- url     : https://prove2.me/theorems/1e043161-8bba-425f-ba0d-2ddcb47971fe
-- title:
--   Explicit rational Euler–Maclaurin enclosure for $\zeta(s)$ on unit-height right rectangles
-- statement:
--   For natural numbers $n, k, K, N$ with $K \ge 1$ and $N \ge 1$, put $d = \frac{1}{k+3}$, $L = 100000 + n$, and consider the closed rectangle
--
--   $$
--   R_{n,k} = \left[\frac{1}{2} + d,\, 1\right] \times [L + d,\, L + 1] \subset \mathbb{C}.
--   $$
--
--   Let $Z_{K,N}(s)$ denote the order-$(2K+1)$ Euler–Maclaurin Dirichlet approximant `ZetaReflection.EMHigh.emFinite K s N` to the Riemann zeta function $\zeta(s)$:
--
--   $$
--   Z_{K,N}(s) = \sum_{j=1}^{N-1} j^{-s} + N^{-s}\left(\frac{N}{s-1} + \frac{1}{2} + \sum_{i=0}^{2K-2} \frac{B_{i+2}\,(s)_{i+1}}{(i+2)!\,N^{i+1}}\right),
--   $$
--
--   where $(s)_r = s(s+1)\cdots(s+r-1)$ is the rising factorial and $B_m$ is the $m$-th Bernoulli number. For every $s \in R_{n,k}$,
--
--   $$
--   |\zeta(s) - Z_{K,N}(s)| \le \frac{(100002 + n + 2K)^{2K+1}}{3 \cdot 6^{2K} \cdot N^{2K}}.
--   $$
--
--   This uniform rational error bound eliminates $\pi$, transcendental gamma/Bernoulli bounds, and complex-argument dependence over the rectangle $R_{n,k}$, making high-height mesh certificates expressible purely in terms of the finite sum $Z_{K,N}(s)$.
--
--   **Formalization Note.** The bound specializes `ZetaReflection.EMHigh.em_zeta_orderK_enclosure_odd` using the explicit rectangle coordinates from `MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates` and packages the upper bound as a cast rational number.
-- source:
--   Specialized from ZetaReflection.EMHigh.em_zeta_orderK_enclosure_odd (https://prove2.me/theorems/63267ad9-d44d-4bd3-a829-be01d0c0cb1d) to the unit-height right rectangles of MasulloRH.unit_height_zeta_right_rectangle_mesh_certificates (https://prove2.me/theorems/f9f6d44b-a148-4b98-8aa0-a911a4eaa8b4), responding to https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-ad8fb92e-0c03-4bee-937c-638f829135a3 .

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem MasulloRH.unit_height_em_enclosure (n k K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
      ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤
        ((((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K)) : ℚ) : ℝ) := by sorry
