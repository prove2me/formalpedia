-- Prove2me | Theorems.Thm_MultibrotCorr_lemma_3_2
-- name    : MultibrotCorr.lemma_3_2
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:32:39.852075+00:00
-- url     : https://prove2.me/theorems/a522183f-2d09-4dde-8910-82f5ea54154c
-- title:
--   Lemma 3.2 — stability and uniqueness of the bounded Misiurewicz orbit
-- statement:
--   For a Misiurewicz parameter $a$, the repelling cycle $\alpha_a$ moves holomorphically with the parameter: on a neighborhood $W$ of $a$ there are holomorphic functions $z_j(c)$ and $\xi(c)=z_0(c)$ with $\xi(a)=a$, $z_j(a)=z_j$, such that $g_c(\xi(c))=z_\ell(c)$, the sequence $(z_j(c))$ is the unique bounded forward orbit of $\xi(c)$ under $\mathbf{f}_c$, its tail $(z_j(c))_{j\ge\ell}$ is the repelling cycle $\alpha(c)$ of period $n$, and the multiplier $\lambda(c)$ is holomorphic. This is the stability of the Misiurewicz uniqueness condition under perturbation.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Lemma 3.2, Section 3; eq. (3.5), (3.6), (3.7), (3.8).

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem lemma_3_2 (e : UnicriticalExponent) (a : ℂ) (ha : IsMisiurewicz e a) :
    ∃ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
      (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ),
      IsMisiurewiczOrbitData e a ℓ n z φ U ∧
      IsMisiurewiczMotion e a ℓ n z φ U W zz lam := by sorry
end MultibrotCorr
