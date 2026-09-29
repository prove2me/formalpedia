-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
-- name    : ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/75af61f8-180b-5e48-8869-d07d87e75fc3
-- title:
--   Winding pairing against dlogΦ modulo the period lattice
-- statement:
--   Let $\Gamma\le SL_2(\mathbb{Z})$ be of finite index with $-1\in\Gamma$, let $\Phi:\mathbb{C}\to\mathbb{C}$, let $S$ be a finite set of points of the upper half plane $\mathcal{H}$ and $n:\mathcal{H}\to\mathbb{Z}$. Assume: at every $\tau\in\mathcal{H}$ one has $\Phi(z)=(z-\tau)^{n(\tau)}\Psi(z)$ near $\tau$ for some $\Psi$ that is $C^1$ at $\tau$ in the real sense with $\Psi(\tau)\neq0$; $\Phi(\gamma\cdot\tau)=\Phi(\tau)$ for all $\gamma\in\Gamma$, $\tau\in\mathcal{H}$; for every $\sigma\in SL_2(\mathbb{Z})$ the function $\tau\mapsto\Phi(\sigma\cdot\tau)$ tends to a non-zero constant as $\operatorname{Im}\tau\to\infty$, and the real Fréchet derivative of $u\mapsto\Phi(\sigma\cdot u)$ tends to $0$ there; $n$ is $\Gamma$-invariant, every $\tau$ with $n(\tau)\neq0$ lies in the $\Gamma$-orbit of some $s\in S$, distinct elements of $S$ are in distinct $\Gamma$-orbits, $\#\mathrm{Stab}_\Gamma(s)\mid 2n(s)$ for $s\in S$, and $\sum_{s\in S}n(s)/\#\mathrm{Stab}_\Gamma(s)=0$. Let $h_T$ be the smoothed fundamental function of $\Gamma$, namely $h_T(z)=\sum_{q\in SL_2(\mathbb{Z})/\Gamma}\mathrm{puCut}\,T$ evaluated at the Möbius image of $z$ under a chosen representative of $q$, and let $E_g(z)=\int_0^1 g\bigl(\mathrm{segmentPath}\,i\,z\,t\bigr)(z-i)\,dt$ be the period of $g\in S_2(\Gamma)$ along the segment from $i$ to $z$. Then, first, for every $T\in\mathbb{R}$ and every $g$ the function $z\mapsto \frac{E_g(z)}{\Phi(z)}\bigl(\partial_1\Phi\,\partial_i h_T-\partial_i\Phi\,\partial_1 h_T\bigr)(z)$ is integrable on $\mathbb{C}$; secondly, there is a $\Lambda$ in the period lattice of $\Gamma$, the $\mathbb{Z}$-span inside the $\mathbb{C}$-dual of $S_2(\Gamma)$ of the periods $g\mapsto E_g(\gamma\cdot i)$ for $\gamma\in\Gamma$, such that for every $g$, as $T\to\infty$, $$\frac{i}{\pi}\int_{\mathbb{C}}\frac{E_g}{\Phi}\bigl(\partial_1\Phi\,\partial_i h_T-\partial_i\Phi\,\partial_1 h_T\bigr)+2\sum_{a\in\mathbb{C}}n(a)E_g(a)h_T(a)\longrightarrow \Lambda(g)+\sum_{s\in S}\frac{2n(s)}{\#\mathrm{Stab}_\Gamma(s)}\,\mathrm{periodAlongOf}\,\Gamma\,i\,s\,(g),$$ the finite sum over $a$ being a finsum.
--
--   This is Riemann's reciprocity law for the winding class $d\log\Phi$ paired against the weight-two cusp forms on $X(\Gamma)$, with the usual fundamental polygon replaced by the smoothed fundamental function $h_T$ and the limit $T\to\infty$: the pairing equals, modulo the period lattice, the Abel–Jacobi term attached to the divisor $\sum_s n(s)\,[s]$. It is used in the proof of [`ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp), where $\Phi$ is the multiplier of an exponential automorphic function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : Γ) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (Γ) T z : ℂ))
    (E : CuspForm (Γ) 2 → ℂ → ℂ)
    (hE : ∀ g z, E g z = ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g) :
    (∀ (T : ℝ) (g : CuspForm (Γ) 2),
      Integrable fun z : ℂ => E g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I - fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ g : CuspForm (Γ) 2,
        Tendsto (fun T : ℝ =>
          Complex.I / Real.pi * (∫ z : ℂ, E g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I -
              fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * E g a * h T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by sorry
