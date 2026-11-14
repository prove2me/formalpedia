-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_fixed_family_gaussian_advantage_transfer
-- name    : InfoLossLAR.WorstCase.fixed_family_gaussian_advantage_transfer
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T16:10:09.985251+00:00
-- url     : https://prove2.me/theorems/8fce3b23-73bf-4f84-b00d-daece3f991e7
-- title:
--   Fixed-family LAR to Gaussian LWE: inverse-polynomial advantage transfer
-- statement:
--   Consider the fixed public family of Section 9.9, with secret dimension $N(\lambda)=\lambda$, Gaussian width $\sigma(\lambda)=\lambda+2$, and the modulus, block dimension and label function defined there. Suppose this family admits fixed-order Gaussian affine fiber transports in the sense of Definition 5.3.
--
--   For every uniform QPT LAR distinguisher $D$, every positive polynomially bounded sample-count function $t$, and every $c\in\mathbb N$, there exist a uniform QPT Gaussian-LWE distinguisher $B$, an exponent $b\in\mathbb N$, and a threshold $\lambda_0$ such that, for every positive $\lambda\ge\lambda_0$,
--
--   $$
--   \lambda^{-c}\le\operatorname{Adv}^{\mathrm{dLAR}}_D(\lambda,t(\lambda))
--   \quad\Longrightarrow\quad
--   \lambda^{-b}\le\operatorname{Adv}^{\mathrm{Gauss\text{-}LWE}}_B(\lambda,t(\lambda)).
--   $$
--
--   Gaussian LWE uses the same public parameters and $t(\lambda)$ blocks of dimension $d(\lambda)$, with error distribution $D_{\mathbb Z^{d(\lambda)},\sigma(\lambda)}\bmod q(\lambda)$. The reduction runs $D$ once on a classically prepared input.
--
--   This isolates the transfer of inverse-polynomial distinguishing advantage from LAR to Gaussian LWE. The reduction and its exponent are independent of any later restriction to an infinite set of security parameters.
--
--   **Formalization Note.** This is the fixed-family consequence of Corollary 5.5 after polynomial-loss absorption, as used in Appendix I.1. Polynomial boundedness of $t$ does not assert its computability. The statement uses the fixed family's published binary encoding of public parameters.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC^0 Pseudorandomness from Worst-Case Lattices, https://arxiv.org/html/2611.05136v1, Corollary 5.5 (p. 25), Section 9.9 (p. 58), Appendix I.1 (pp. 132–133).

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- Corollary 5.5 and polynomial-loss absorption for the fixed family of Section 9.9.
The distinguisher and advantage exponent are chosen before any success subsequence. -/
theorem fixed_family_gaussian_advantage_transfer
    (hAFT : AdmitsFixedOrderGaussianAFT famInput famq famd (fun _ => 1)
      (fun lam => (famσ lam : ℝ)) famLabel)
    (D : Family) (hD : IsQPT D)
    (t : ℕ → ℕ) (ht : ∀ lam, 1 ≤ t lam) (htp : PolyBoundedFn t) (c : ℕ) :
    ∃ B : Family, IsQPT B ∧ CallsOnce B D ∧ ∃ b lam₀ : ℕ,
      ∀ lam : ℕ, lam₀ ≤ lam → 1 ≤ lam →
        (lam : ℝ) ^ (-(c : ℝ)) ≤ famAdvLAR D lam (t lam) →
        (lam : ℝ) ^ (-(b : ℝ)) ≤
          advLWE B lam (famPP lam) (famq lam) (famN lam) (famd lam) (t lam)
            (chiG (famq lam) (famd lam) (famσ lam)) := by sorry

end InfoLossLAR.WorstCase
