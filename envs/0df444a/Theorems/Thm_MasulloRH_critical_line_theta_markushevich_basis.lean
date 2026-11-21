-- Prove2me | Theorems.Thm_MasulloRH_critical_line_theta_markushevich_basis
-- name    : MasulloRH.critical_line_theta_markushevich_basis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:45:32.913494+00:00
-- url     : https://prove2.me/theorems/8883e9ac-4be9-4346-9087-8039866025ae
-- title:
--   A Markushevich basis of critical-line zeta jets on the rational theta annihilator
-- statement:
--   For each real weight $p>1/2$, let $E_p$ be the Hilbert annihilator of all admissible rational real-place theta tests. Index the distinct zeros $\rho=1/2+i\gamma$ of the Riemann zeta function by their actual locations. Attach an integer $r\ge0$ to $\rho$ whenever $r<\operatorname{ord}_{\rho}\zeta$ and $r+1/2<p$. This index set is countable. The vectors represented in $L^2(\mathbb R,dx)$ by $(1+x^2)^{-p/2}x^r e^{i\gamma x}$ have dense linear span in $E_p$. They admit continuous complex-linear coordinate functionals on $E_p$ with Kronecker-delta pairings, and the common kernel of those functionals is zero. Thus they form a Markushevich basis.
-- source:
--   A. M. Masullo, The Music of the Primes, Theorem 10.2.1.1 and Remark 10.2.1.2, pp. 440–441, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This gives the rational norm-coordinate result on the critical line, in the realization s=2p with the strict square-integrability condition r+1/2<p. Uses the proved rational theta annihilator identification 5f60b4c6 and Sobolev spectral synthesis 50593736. The coalescing-zero result 6bc4810d and the accompanying critical_line_no_uniform_biorthogonal_product audit address products of primal and dual norms in §10.3.

import Definitions.Def_MasulloRH_RationalThetaSpace
open MeasureTheory MasulloRH
open scoped Topology Classical

theorem MasulloRH.critical_line_theta_markushevich_basis (p : ℝ) (hp : 1/2<p) :
    let Z := {ρ : ℂ // riemannZeta ρ=0 ∧ ρ.re=1/2}
    let I := Σ ρ : Z, Fin (min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊)
    Countable I ∧ ∃ (v : I → rationalThetaAnnihilator p) (ℓ : I → rationalThetaAnnihilator p →L[ℂ] ℂ),
      (∀ i : I, ((v i).val : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
        ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^i.2.val * Complex.exp (↑(i.1.val.im*x)*Complex.I))) ∧
      (∀ i : I, ℓ i (v i) = 1) ∧ (∀ i j : I, i ≠ j → ℓ i (v j)=0) ∧
      Dense (Submodule.span ℂ (Set.range v) : Set (rationalThetaAnnihilator p)) ∧
      (∀ u : rationalThetaAnnihilator p, (∀ i : I, ℓ i u=0) → u=0) := by sorry
