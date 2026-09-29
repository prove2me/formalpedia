-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left
-- name    : LanglandsTunnell.TateLocal.tateFourier_comp_mul_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/3d5ebe77-a828-5c61-aa26-c1d139dfc6f4
-- title:
--   Dilation rule for the local Tate Fourier transform
-- statement:
--   Let $K$ be a field carrying a topology making it a topological ring, locally compact, with a measurable space structure that is the Borel structure of its topology. Let $\psi : K \to \mathbb{C}$ be an additive character, and let $\mu$ be a measure on $K$ which is an additive Haar measure and is regular. Let $f : K \to \mathbb{C}$ be an arbitrary function, let $a \in K$ with $a \neq 0$, and let $y \in K$. Writing $\mathrm{tateFourier}\,\psi\,\mu\,f\,(y) = \int_K f(x)\,\psi(xy)\,d\mu(x)$ (a Bochner integral, hence $0$ when the integrand fails to be integrable), and $\mathrm{modulus}(a) \in \mathbb{R}_{\geq 0}$ for the value of the distributive Haar character $\mathrm{distribHaarChar}\,K$ at the unit $a$ (and $0$ at $a = 0$), the assertion is the identity
--   $$\int_K f(ax)\,\psi(xy)\,d\mu(x) \;=\; \mathrm{modulus}(a)^{-1} \int_K f(x)\,\psi(x\,a^{-1}y)\,d\mu(x),$$
--   the scalar $\mathrm{modulus}(a)^{-1}$ being taken in $\mathbb{R}$ and then mapped to $\mathbb{C}$. No continuity, integrability or measurability hypothesis on $\psi$ or $f$ is imposed.
--
--   This is the dilation (homogeneity) rule of Tate's local Fourier transform: transforming a function dilated by $a$ rescales the variable by $a^{-1}$ and introduces the factor $|a|^{-1}$, where $|a|$ is the module of $a$ attached to the Haar measure of the locally compact field $K$. It is used in the local Rankin–Selberg and Kirillov-model computations of the project, for instance in the conductor estimates for Fourier transforms of shell kernels and in the construction of dual middle data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.TateLocal.tateFourier_comp_mul_left (K : Type*) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (ψ : AddChar K ℂ) (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (f : K → ℂ) (a : K)
    (ha : a ≠ 0) (y : K) :
    tateFourier ψ μ (fun x => f (a * x)) y
      = ((modulus a : ℝ) : ℂ)⁻¹ * tateFourier ψ μ f (a⁻¹ * y) := by sorry
