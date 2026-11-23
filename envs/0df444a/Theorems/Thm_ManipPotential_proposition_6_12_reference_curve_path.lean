-- Prove2me | Theorems.Thm_ManipPotential_proposition_6_12_reference_curve_path
-- name    : ManipPotential.proposition_6_12_reference_curve_path
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:47:33.377224+00:00
-- url     : https://prove2.me/theorems/67a0e837-310f-4b2b-bd4c-5e78a4693812
-- title:
--   The reference curve produces a rational transfer path from $c_i$ to $c_j$
-- statement:
--   Assume the setup of Proposition 6.12, Step 1: $g$ satisfies the three axioms of Lemma 6.2, $G$ is
--   differentiable at $z_0\in U$, every $G(z)$ for $z\in U$ is a common junction with all coordinates
--   greater than $1$, and $c_i\ne c_j$. With $D=DG(z_0)$, $T=\operatorname{im}D$, and
--   $C=\operatorname{span}_{\ge0}(\mathcal T_{ij})$, suppose the (eventually forbidden) membership
--   $$
--   -(\ell_i-\ell_j)\in\operatorname{cl}(C+T).
--   $$
--   Then the reference-curve construction produces a finite sequence of rational profiles
--   $Q_0,\ldots,Q_L$ such that
--   $$
--   g(Q_0)=c_i,\qquad g(Q_L)=c_j,\qquad g(Q_k)\in\{c_i,c_j\}\quad(0\le k\le L),
--   $$
--   and every consecutive pair is a positive transfer step from Eq. (17) with nonnegative replacement
--   background.
--
--   This statement isolates the analytic and approximation portion of Step 1. It includes selecting the
--   nearby vector and rational transfer coefficients, choosing the round count and a sufficiently small
--   rational $\rho$, applying the uniform differentiability estimate, and invoking Lemma 6.10 at the round
--   points of the reference curve. It deliberately does not include the final contradiction with bounded
--   manipulation potential, which is a separate finite-path lemma.
--
--   **Formalization Note** The path is encoded by `Q : ℕ → Ranking m → ℚ` up to a finite length `L`. The
--   closure-membership hypothesis is written using the same submodules and coercions as the parent
--   statement; `TransferStep` records both the profile increment and positivity of its replacement
--   background.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, pp.35–37: reference curve $B_\rho(t)$, rational approximation and transfer rounds, and endpoint supports; uses Lemma 6.10, pp.32–33.

import Mathlib
import Definitions.Def_ManipPotential_GAxioms
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_IsCommonJunction
import Definitions.Def_ManipPotential_TransferStep

open scoped NNReal Pointwise

/-- If the negative cyclic difference belongs to the closed transfer-plus-derivative cone,
the reference-curve construction gives a finite rational transfer path with forbidden endpoint
winners. -/
theorem ManipPotential.proposition_6_12_reference_curve_path {m : ℕ} [NeZero m] (hm : 3 ≤ m) (K : ℕ)
    (g : (Ranking m → ℚ) → Fin m) (hg : GAxioms K g)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hUopen : IsOpen U)
    (z₀ : ((ExtRanking m → ℝ) × ℝ)) (hzU : z₀ ∈ U)
    (hzdiff : DifferentiableAt ℝ G z₀)
    (hJ : ∀ z ∈ U, IsCommonJunction g (G z))
    (hpos : ∀ z ∈ U, ∀ r, 1 < G z r) (i j : Fin m) (hij : i ≠ j)
    (hmem :
      let D : ((ExtRanking m → ℝ) × ℝ) →ₗ[ℝ] (Ranking m → ℝ) :=
        (fderiv ℝ G z₀).toLinearMap
      let T : Submodule ℝ (Ranking m → ℝ) := LinearMap.range D
      let C : Submodule ℝ≥0 (Ranking m → ℝ) :=
        Submodule.span ℝ≥0 (TransferVectors ((K : ℝ) + 1) i j)
      (-(unitVec (ell i) - unitVec (ell j))) ∈
        closure ((C : Set (Ranking m → ℝ)) + (T : Set (Ranking m → ℝ)))) :
    ∃ (L : ℕ) (Q : ℕ → Ranking m → ℚ),
      g (Q 0) = i ∧ g (Q L) = j ∧
      (∀ k ≤ L, g (Q k) = i ∨ g (Q k) = j) ∧
      (∀ k < L, TransferStep K i j (Q k) (Q (k + 1))) := by sorry
