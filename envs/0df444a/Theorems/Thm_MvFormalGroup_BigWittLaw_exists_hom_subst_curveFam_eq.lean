-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq
-- name    : MvFormalGroup.BigWittLaw.exists_hom_subst_curveFam_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/24c98592-45cf-5b0a-932f-449236534a05
-- title:
--   Every curve arises from a big Witt homomorphism
-- statement:
--   Let $R$ be a commutative ring, $d$ a natural number, and $\Phi$ a $d$-dimensional formal group law over $R$, that is, a $d$-tuple $\Phi_1,\dots,\Phi_d$ of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, linear coefficients $\delta_{ij}$ on each of the two blocks of variables, and satisfying the associativity substitution identity; assume moreover `Φ.IsComm`, i.e. interchanging the two blocks of variables fixes each $\Phi_i$. Let $\gamma : \mathrm{Fin}\,d \to R[[t]]$ be a $d$-tuple of one-variable power series with $\gamma_j(0)=0$. Then there exists a $d$-tuple $G : \mathrm{Fin}\,d \to R[[a_0,a_1,\dots]]$ of power series in countably many variables indexed by $\mathbb{N}$ such that: each $G_j$ has zero constant term; substituting into $G_j$ the big Witt addition family $\Sigma_n = a_n + b_n + \sum_{i<n} a_i b_{n-1-i}$ (variables indexed by $\mathrm{Fin}\,2 \times \mathbb{N}$, i.e. $a_n = X_{(0,n)}$, $b_n = X_{(1,n)}$) gives the same series as substituting into $\Phi_j$ the family consisting of the $G_l(a)$ in the first block of variables and the $G_l(b)$ in the second; and substituting into $G_j$ the family sending $0 \mapsto X$ and every $n+1 \mapsto 0$ yields $\gamma_j$.
--
--   This is the existence half of Cartier's first theorem, that the big Witt formal group $\widehat\Lambda$ represents the functor of curves on a commutative formal group law, the universal curve being $1+tT$; uniqueness of $G$ is not asserted here. It underlies the construction of Cartier-module structures in the project and is used for the results on substitution of $p$-th power families, on curves determined by their images, and on surjectivity of the tangent map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.exists_hom_subst_curveFam_eq
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    ∃ G : Fin d → MvPowerSeries ℕ R,
      (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
          MvPowerSeries.subst
            (Sum.elim
              (fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
              fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
            (Φ.toPowerSeries j)) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.CartierModule.curveFam R) (G j) = γ j) := by sorry
