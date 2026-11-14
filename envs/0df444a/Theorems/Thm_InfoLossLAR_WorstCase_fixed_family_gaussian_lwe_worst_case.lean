-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_fixed_family_gaussian_lwe_worst_case
-- name    : InfoLossLAR.WorstCase.fixed_family_gaussian_lwe_worst_case
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T16:10:06.6598+00:00
-- url     : https://prove2.me/theorems/e07e3b3b-5a03-440e-a86e-79bca30a61af
-- title:
--   Fixed-family Gaussian LWE to quantum worst-case GapSVP and SIVP
-- statement:
--   For the fixed public family of Section 9.9, there exist constants $C,k\in\mathbb N$, with $C\ge1$, satisfying the following statement. Let $B$ be a uniform QPT Gaussian block-LWE distinguisher, let $t$ be a positive polynomially bounded block-count function, let $b\in\mathbb N$, and let $S$ be an infinite set of positive security parameters. Suppose that, for all sufficiently large $\lambda\in S$,
--
--   $$
--   \operatorname{Adv}^{\mathrm{Gauss\text{-}LWE}}_B(\lambda,t(\lambda))\ge\lambda^{-b},
--   $$
--
--   where the block error distribution is $D_{\mathbb Z^{d(\lambda)},\sigma(\lambda)}\bmod q(\lambda)$ and the distinguisher receives the fixed family's public parameters.
--
--   There exist uniform quantum polynomial-time algorithms solving worst-case $\mathrm{GapSVP}_{\gamma(\lambda)}$ and $\mathrm{SIVP}_{\gamma(\lambda)}$, respectively, in dimension $N(\lambda)=\lambda$, for every $\lambda\in S$, where
--
--   $$
--   \gamma(\lambda)=Cq(\lambda)(\log_2(\lambda+2))^k.
--   $$
--
--   The algorithms satisfy the published worst-case success requirements on every nonsingular integer-basis instance. The constants $C,k$ are fixed before $B,t,b,S$.
--
--   This is the Gaussian-LWE interface to the quantum worst-case lattice reduction, independent of LAR and affine fiber transport.
--
--   **Formalization Note.** The hypothesis only requires advantage eventually on $S$, whereas the conclusion includes all positive dimensions in $S$. Finitely many exceptional dimensions are included using exact fixed-dimensional lattice algorithms. No computability hypothesis is imposed on $t$ or $S$. Quantum algorithms and their success probabilities use the published uniform Clifford+T circuit model on binary-coded classical inputs.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC^0 Pseudorandomness from Worst-Case Lattices, https://arxiv.org/html/2611.05136v1, Section 9.9 (p. 58), Appendix I.1 (pp. 132–133), using the cited Peikert full-version Theorem 3.1 and Regev full-version Theorem 3.1, Lemmas 4.1–4.2, 3.11 and 3.14. Finite-dimensional patch makes the source asymptotic guarantee valid at every positive parameter in S.

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems

set_option autoImplicit false

open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase

/-- The Gaussian interface and quantum worst-case reduction in Appendix I.1,
independent of LAR and affine fiber transport. Finite exceptional dimensions are included. -/
theorem fixed_family_gaussian_lwe_worst_case :
    ∃ C k : ℕ, 1 ≤ C ∧ ∀ B : Family, IsQPT B →
      ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        ∀ b : ℕ, ∀ S : Set ℕ, S.Infinite → (∀ lam ∈ S, 1 ≤ lam) →
          (∃ lam₀ : ℕ, ∀ lam ∈ S, lam₀ ≤ lam →
            (lam : ℝ) ^ (-(b : ℝ)) ≤
              advLWE B lam (famPP lam) (famq lam) (famN lam) (famd lam) (t lam)
                (chiG (famq lam) (famd lam) (famσ lam))) →
            (∃ A : Family, IsQPT A ∧ ∀ lam ∈ S,
              SolvesGapSVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) ∧
            (∃ A : MFamily, IsMQPT A ∧ ∀ lam ∈ S,
              SolvesSIVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) := by sorry

end InfoLossLAR.WorstCase
