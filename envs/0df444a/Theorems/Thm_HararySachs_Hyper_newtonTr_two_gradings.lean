-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_two_gradings
-- name    : HararySachs.Hyper.newtonTr_two_gradings
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:02:46.07998+00:00
-- url     : https://prove2.me/theorems/c2eb6581-36c4-4cf2-bdd6-32bb40253ef5
-- title:
--   Total-degree versus row-degree logarithms of a polynomial
-- statement:
--   Let $Q$ be a polynomial over $\mathbb{Q}$ in any set of variables, with constant term $1$, and let $w$ be a weight on the variables. Write $[\,\cdot\,]_D$ for the homogeneous component of total degree $D$ and $[\,\cdot\,]^{w=m}$ for the $w$-weighted homogeneous component of degree $m$. Put $C = [Q]^{w=0}$ and $q_j = [Q]^{w=j}$.
--
--   1. Let $\tau_d$ be the Newton traces of $\Phi(z) = \sum_d [Q]_d\, z^d$, so that $\log Q = -\sum_{d\ge 1}\tau_d/d$ by total degree.
--   2. Let $S_m$ be the $m$-th Newton trace of $\widehat\Phi(s) = 1 + \sum_{j=1}^{m} C^{\,j-1} q_j s^j$, so that $S_m = C^m\sigma_m$ where $\log Q = \log C - \sum_{m\ge1}\sigma_m/m$ by $w$-degree.
--
--   Then for every $m$ and $D$,
--   $$[S_m]_D = \sum_{d=0}^{D} \bigl[C^m\bigr]_{D-d}\cdot\frac{m}{d}\,[\tau_d]^{w=m},$$
--   with the convention $m/0 = 0$.
--
--   This polynomial identity compares the two expansions of $\log Q$ without using formal power series. Since $[C^m]_0 = 1$, it determines the row-graded pieces $[\tau_d]^{w=m}$ recursively from the numerators $S_m$. It is used to transfer the row-invariance of $S_m$ to the Newton traces.
--
--   **Formalization Note** $\Phi$ is given with the hypothesis that its coefficients are the homogeneous components of $Q$. $\widehat\Phi$ is `hatPhi C q m`, and the weight $w$ is arbitrary.
-- source:
--   Logarithmic derivative identities for a polynomial with constant term 1 under two compatible gradings; used in the degree-preserving variant of Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Proposition I (mission strategy comments 2173f2a9-fd2e-4d5e-afb5-27607d970161 and 8357894d-0c47-45af-94e5-d71263b245a7).

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Definitions.Def_HararySachs_Hyper_RowProj

namespace HararySachs.Hyper

theorem newtonTr_two_gradings {σ : Type*} (w : σ → ℕ) (Q : MvPolynomial σ ℚ)
    (hQ : MvPolynomial.constantCoeff Q = 1)
    (Φ : Polynomial (MvPolynomial σ ℚ))
    (hΦ : ∀ d, Φ.coeff d = MvPolynomial.homogeneousComponent d Q) (m D : ℕ) :
    MvPolynomial.homogeneousComponent D
        (newtonTr (hatPhi (MvPolynomial.weightedHomogeneousComponent w 0 Q)
          (fun j => MvPolynomial.weightedHomogeneousComponent w j Q) m) m) =
      ∑ d ∈ Finset.range (D + 1),
        MvPolynomial.homogeneousComponent (D - d)
            ((MvPolynomial.weightedHomogeneousComponent w 0 Q) ^ m) *
          (((m : ℚ) / d) • MvPolynomial.weightedHomogeneousComponent w m (newtonTr Φ d)) := by
  sorry

end HararySachs.Hyper
