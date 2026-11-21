-- Prove2me | Theorems.Thm_MultibrotCorr_theorem_4_1
-- name    : MultibrotCorr.theorem_4_1
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:34:15.917542+00:00
-- url     : https://prove2.me/theorems/908c409c-2386-40e6-beab-b71bb82e9da2
-- title:
--   Theorem 4.1 (Theorem A) — asymptotic self-similarity of $K_c$ near a Misiurewicz point
-- statement:
--   Let $a$ be a Misiurewicz point. For every parameter $c$ in a neighborhood of $a$, the filled Julia set $K_c$ is asymptotically $\lambda(c)$-self-similar about each point $z_j(c)$ of the perturbed orbit (1.2), with limit model $B_j(c)$ defined inductively by $B_\ell(c)=\varphi_c(\overline V\cap K_c)$ and $B_j(c)=f'_{j,c}(z_{j-1}(c))\cdot B_{j-1}(c)$ (eq. 4.2). In particular $K_a$ is asymptotically self-similar about $a$ and about every point of the repelling cycle $\alpha_a$. The motion and Kœnigs linearization are those of Lemma 3.2 and Remark 4.1.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Theorem 4.1 (Theorem A), Section 4; eq. (4.2), Remark 4.1.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem theorem_4_1 (e : UnicriticalExponent) (a : ℂ) (ha : IsMisiurewicz e a) :
    ∃ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
      (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ)
      (φK : ℂ → ℂ → ℂ) (φdom : ℂ → Set ℂ),
      IsMisiurewiczOrbitData e a ℓ n z φ U ∧
      IsMisiurewiczMotion e a ℓ n z φ U W zz lam ∧
      IsKoenigsFamily e ℓ n φ zz lam W φK φdom ∧
      ∀ c ∈ W, ∀ j : ℕ, ∀ V : Set ℂ, IsOpen V → zz ℓ c ∈ V → closure V ⊆ φdom c →
        IsAsymptoticallySelfSimilar (filledJulia e c) (zz j c) (lam c)
          (limitModelB e ℓ zz φK c V j) := by sorry
end MultibrotCorr
