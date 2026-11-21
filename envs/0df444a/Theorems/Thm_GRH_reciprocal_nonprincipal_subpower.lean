-- Prove2me | Theorems.Thm_GRH_reciprocal_nonprincipal_subpower
-- name    : GRH.reciprocal_nonprincipal_subpower
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:27:20.274201+00:00
-- url     : https://prove2.me/theorems/002e2873-7fe9-49e9-aa82-096600ec5d26
-- title:
--   Subpower reciprocal growth of nonprincipal Dirichlet L-functions inside the fixed zero-free half-plane
-- statement:
--   Let $\theta=0.8749570698$. For any nonprincipal Dirichlet character $\chi$ of positive modulus, any $\delta,\varepsilon>0$, and $\theta+\delta\le\operatorname{Re}s\le2$, $|\operatorname{Im}s|\ge1$, the reciprocal of its analytically continued $L$-function satisfies
--   $$|1/L(s,\chi)|\le C_{\chi,\delta,\varepsilon}|\operatorname{Im}s|^\varepsilon.$$
--   This is the subpower growth hypothesis in the holomorphic Perron estimate for finite twisted Möbius sums.
-- source:
--   The normalized logarithm and small-disk proof adapt the platform proof of Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis https://prove2.me/theorems/242af0ad-5520-48fe-b514-c52cefbcd1c2. The disk estimate is https://prove2.me/theorems/4636708a-d1f1-4d25-8f1f-7b99460a4b70. The Dirichlet-specific outer growth input is https://prove2.me/theorems/c5c90f21-b770-4fe2-aad6-2ead5f8ee9c0, and the zero-free boundary is https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex

theorem GRH.reciprocal_nonprincipal_subpower (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ s : ℂ, (0.8749570698:ℝ) + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(χ.LFunction s)⁻¹‖ ≤ C * |s.im|^ε := by sorry
