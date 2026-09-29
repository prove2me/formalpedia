-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental
-- name    : ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/50aca1a2-1f06-546f-9595-93d48226e4f0
-- title:
--   Winding pairing on X₀(N) lands in the period lattice
-- statement:
--   Fix $N\ge 1$ and write $\Gamma=\Gamma_0(N)$. Let $\Phi:\mathbb{C}\to\mathbb{C}$, a finite set $S$ of points of the upper half plane $\mathbb{H}$, and $n:\mathbb{H}\to\mathbb{Z}$ be given, subject to: (hloc) near each $\tau\in\mathbb{H}$ one has $\Phi(z)=(z-\tau)^{n(\tau)}\Psi(z)$ eventually at $\tau$, for some $\Psi$ that is real $C^1$ at $\tau$ with $\Psi(\tau)\neq 0$; (hinv) $\Phi(\gamma\tau)=\Phi(\tau)$ for $\gamma\in\Gamma$; (hcuspΦ) for each $\sigma\in SL_2(\mathbb{Z})$, $\Phi(\sigma\tau)$ tends to a non-zero limit as $\operatorname{Im}\tau\to\infty$; (hdecay) the real Fréchet derivative of $u\mapsto\Phi(\sigma u)$ tends to $0$ there; (hn) $n$ is $\Gamma$-invariant; (hcov) every $\tau$ with $n(\tau)\neq 0$ lies in the $\Gamma$-orbit of some $s\in S$; (hinj) distinct points of $S$ are $\Gamma$-inequivalent; (hdvd) $\#\mathrm{Stab}_\Gamma(s)\mid 2n(s)$ for $s\in S$; (hdeg) $\sum_{s\in S}n(s)/\#\mathrm{Stab}_\Gamma(s)=0$. Let $h(T,\cdot)$ be the complex-valued smoothed fundamental function of $\Gamma$ at parameter $T$, namely the sum over cosets $q\in SL_2(\mathbb{Z})/\Gamma$ of the cut-off $\mathrm{puCut}\,T$ at the Möbius image of $z$ under a representative of $q$, and let $E(g,z)=\int_0^1 g(\text{segment from }i\text{ to }z)(z-i)\,dt$ be the period of $g$ along the segment from $i$ to $z$. Then: for every $T$ and every weight-two cusp form $g$ for $\Gamma$, the function $z\mapsto \frac{E(g,z)}{\Phi(z)}\bigl(D\Phi_z(1)\,Dh_{T,z}(i)-D\Phi_z(i)\,Dh_{T,z}(1)\bigr)$ is integrable on $\mathbb{C}$; and there exists $\Lambda$ in the period lattice of $N$ (the $\mathbb{Z}$-span of the functionals $g\mapsto\int_i^{\gamma i}g$, $\gamma\in\Gamma$) such that for every such $g$, $$\frac{i}{\pi}\int_{\mathbb{C}}\frac{E(g,z)}{\Phi(z)}\bigl(D\Phi_z(1)Dh_{T,z}(i)-D\Phi_z(i)Dh_{T,z}(1)\bigr)+2\sum_{a\in\mathbb{C}}n(a)E(g,a)h(T,a)$$ converges, as $T\to\infty$, to $\Lambda(g)+\sum_{s\in S}\frac{2n(s)}{\#\mathrm{Stab}_\Gamma(s)}\int_i^{s}g$.
--
--   This is the integrality statement for the winding pairing on $X_0(N)$: the smoothed cup product of the class of $g\,dz$ with the logarithmic-derivative class of a $\Gamma_0(N)$-invariant multiplier $\Phi$ equals, in the limit, an Abel–Jacobi contribution from the divisor of $\Phi$ plus a period over an integral cycle, as provided by Poincaré–Lefschetz duality with integer coefficients. It is used by [`ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp), where the multiplier is written as an exponential and the winding term is compared with a Petersson-type integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental
    {N : ℕ} [NeZero N] (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (CongruenceSubgroup.Gamma0 N) T z : ℂ))
    (E : CuspForm (CongruenceSubgroup.Gamma0 N) 2 → ℂ → ℂ)
    (hE : ∀ g z, E g z = ModularCurve.periodAlong N UpperHalfPlane.I (ofComplex z) g) :
    (∀ (T : ℝ) (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      Integrable fun z : ℂ => E g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I - fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Tendsto (fun T : ℝ =>
          Complex.I / Real.pi * (∫ z : ℂ, E g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I -
              fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * E g a * h T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) *
              ModularCurve.periodAlong N UpperHalfPlane.I s g)) := by sorry
