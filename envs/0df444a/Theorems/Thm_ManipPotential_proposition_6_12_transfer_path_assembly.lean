-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_transfer_path_assembly
-- name    : ManipPotential.proposition_6_12_transfer_path_assembly
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:59.371147+00:00
-- url     : https://prove2.me/theorems/6bc04773-9e70-4844-aeee-2b6871a111a6
-- title:
--   Uniform reference-curve approximation and rational transfer-path assembly
-- statement:
--   Let $G$ be differentiable at $z_0\in U$, with all coordinates of $G(z)$ greater than $1$ on the open set $U$. Suppose $u_1,\ldots,u_q$ are transfer vectors in $\mathcal T_{ij}$, $\beta_h\ge0$ are rational, and, with $\eta=1/(64\kappa)$,
--   $$
--   \left\|\sum_h\beta_hu_h-(DG(z_0)v-(\ell_i-\ell_j))\right\|_\infty<\eta.
--   $$
--   Then there are a positive rational $\rho$ and a finite sequence $Q_0,\ldots,Q_L$ of rational profiles with the following properties. Every consecutive pair is a positive transfer step (17) with nonnegative replacement background. The whole line segment $z_0+t\rho v$, $0\le t\le1$, lies in $U$, and $\varepsilon=\rho/(4\kappa)<\tfrac12$. Every visited $Q_k$ is within $\varepsilon/4$ in supremum norm of $B_\rho(t)$ for some $0\le t\le1$; moreover $Q_0$ and $Q_L$ satisfy this estimate at $t=0$ and $t=1$, respectively.
--
--   This packages the analytic and discrete heart of pp.36–37: choose $N$ large, choose $\rho$ so that the uniform differentiability remainder and all replacement blocks are $O(\rho)$, perform the same $q$ moves for $N$ rounds, and combine the four errors of size less than $\eta\rho$. It deliberately leaves the determination of winners to Lemma 6.10.
--
--   **Formalization Note** The intermediate round assigned to a visited profile is existentially quantified, so the statement does not prescribe a particular enumeration or the treatment of zero-coefficient moves. The conclusion $\varepsilon<\tfrac12$ records the smallness condition needed by Lemma 6.10.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, pp.36–37: uniform estimate for $B_\rho(t)$, choice of $N$ and $\rho$, $N$ transfer rounds, four-term error bound, positive replacement backgrounds (footnote 18), and $\varepsilon<\tfrac12$.

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_TransferStep
import Definitions.Def_ManipPotential_referenceCurve

namespace ManipPotential

/-- The uniform derivative estimate and `N` rounds of rational transfer moves produce a path that
tracks the reference curve to order `ε/4`, with positive replacement backgrounds. -/
theorem proposition_6_12_transfer_path_assembly {m : ℕ} [NeZero m]
    (K : ℕ) (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hUopen : IsOpen U)
    (z₀ : ((ExtRanking m → ℝ) × ℝ)) (hzU : z₀ ∈ U)
    (hzdiff : DifferentiableAt ℝ G z₀)
    (hpos : ∀ z ∈ U, ∀ r, 1 < G z r) (i j : Fin m) (hij : i ≠ j)
    (v : ((ExtRanking m → ℝ) × ℝ)) (q : ℕ)
    (u : Fin q → Ranking m → ℝ) (β : Fin q → ℚ)
    (hu : ∀ h, u h ∈ TransferVectors ((K : ℝ) + 1) i j)
    (hβ : ∀ h, 0 ≤ β h)
    (herr : ‖(∑ h, (β h : ℝ) • u h) -
      ((fderiv ℝ G z₀) v - (unitVec (ell i) - unitVec (ell j)))‖ <
        1 / (64 * kappa m K)) :
    ∃ (ρ : ℚ) (L : ℕ) (Q : ℕ → Ranking m → ℚ),
      0 < ρ ∧
      (ρ : ℝ) / (4 * kappa m K) < 1 / 2 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, z₀ + (t * (ρ : ℝ)) • v ∈ U) ∧
      (∀ k ≤ L, ∃ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(fun r => (Q k r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) t‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4) ∧
      ‖(fun r => (Q 0 r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) 0‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4 ∧
      ‖(fun r => (Q L r : ℝ)) - referenceCurve K G z₀ v i j (ρ : ℝ) 1‖ <
          ((ρ : ℝ) / (4 * kappa m K)) / 4 ∧
      (∀ k < L, TransferStep K i j (Q k) (Q (k + 1))) := by sorry
