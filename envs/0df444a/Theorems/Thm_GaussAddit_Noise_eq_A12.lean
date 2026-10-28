-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_A12
-- name    : GaussAddit.Noise.eq_A12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:40.663283+00:00
-- url     : https://prove2.me/theorems/1deda252-1dea-4034-a4f1-c5eb320ed247
-- title:
--   Eq. (A12) (= Eq. (33)) — the Gaussian average (A8) of D(−ν) is Fock-diagonal with entries (2/n)/(2d+|e|²)·((2d−|e|²)/(2d+|e|²))^p
-- statement:
--   Let $n>0$, let $d,e\in\mathbb C$ with $\mathrm{Re}\,d>0$ and $e\neq0$, and let $D(\nu)=\exp(\nu b^\dagger-\nu^*b)$ be the displacement of a single mode $b$ with Fock states $|p\rangle$. For all $p,q\in\mathbb N$ the function $\nu\mapsto e^{-d|\nu|^2/|e|^2}\langle p|D(-\nu)|q\rangle$ is integrable with respect to $d^2\nu=d\,\mathrm{Re}\,\nu\;d\,\mathrm{Im}\,\nu$, and
--   $$\langle p|\Theta|q\rangle:=\int d^2\nu\,\frac{e^{-d|\nu|^2/|e|^2}}{\pi n|e|^2}\,\langle p|D(-\nu)|q\rangle=\frac{2/n}{2d+|e|^2}\left(\frac{2d-|e|^2}{2d+|e|^2}\right)^{p}\delta_{pq}.$$
--
--   With $d=d_j$, $e=e_j$ the eigenvalues of (29), this is (33): each factor $\Theta_{jr}$ of the operator $\Theta$ is diagonal in the Fock basis of its mode, with the vacuum eigenvalue of largest modulus, which is how $\lambda_0$ of (34) is identified.
--
--   **Formalization Note.** $\langle p|D(-\nu)|q\rangle$ is the normal-ordered closed form of the referenced definition module. The integral is against Lebesgue measure on $\mathbb C\cong\mathbb R^2$.
--
--   Differences from the source:
--   - generalization: Fock states with p ⩾ q → all p, q ∈ ℕ; reason: the case p < q follows by complex conjugation; specializes to the printed range
--   - generalization: d = d_j = 1/n + iξ_j and e = e_j ≠ 0 the eigenvalues of (29) → any d with Re d > 0 and any e ≠ 0; reason: the derivation uses only Re d > 0 (the paper's 'positive real part') and e ≠ 0 (the case e_1 = 0 is (36)); the eigenvalues are instances
--   - encoding: ⟨p|Θ|q⟩, Θ = Θ_jr of (32) → the defining integral (A8) itself; reason: (A8) defines ⟨p|Θ|q⟩; the operator is not needed to state the identity
--   - encoding: integral in (A8) → explicit integrability conclusion plus the Bochner integral; reason: a non-integrable integrand would have the junk integral 0
--   - encoding: (A8) and (A12) written with 1/n (defined only for n > 0) → hypothesis 0 < n; reason: excludes only n = 0, where the printed formula is undefined (P_n of (7) divides by n)
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 8, eqs. (A8), (A12); the same identity is eq. (33), p. 4

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_A12 (n : ℝ) (hn : 0 < n) (d e : ℂ) (hd : 0 < d.re) (he : e ≠ 0) (p q : ℕ) :
    Integrable (fun ν : ℂ =>
        Complex.exp (-(d * ((‖ν‖ ^ 2 : ℝ) : ℂ) / ((‖e‖ ^ 2 : ℝ) : ℂ))) * displacementMatrix (-ν) p q) ∧
      ((1 / (Real.pi * n * ‖e‖ ^ 2) : ℝ) : ℂ) *
          ∫ ν : ℂ, Complex.exp (-(d * ((‖ν‖ ^ 2 : ℝ) : ℂ) / ((‖e‖ ^ 2 : ℝ) : ℂ))) *
            displacementMatrix (-ν) p q =
        ((2 / n : ℝ) : ℂ) / (2 * d + ((‖e‖ ^ 2 : ℝ) : ℂ)) *
          ((2 * d - ((‖e‖ ^ 2 : ℝ) : ℂ)) / (2 * d + ((‖e‖ ^ 2 : ℝ) : ℂ))) ^ p *
            (if p = q then 1 else 0) := by sorry

end GaussAddit.Noise
