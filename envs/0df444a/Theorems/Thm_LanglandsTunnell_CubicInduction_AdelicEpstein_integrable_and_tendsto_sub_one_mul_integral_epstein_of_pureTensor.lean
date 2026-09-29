-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/4ca0eba6-f94c-5320-afa4-889fa861a085
-- title:
--   Pole of the GL₃ Epstein integral against |φ|²
-- statement:
--   Work over $\mathbb{Q}$, writing $\mathbb{A}$ for the adele ring of $\mathbb{Q}$ and $\widehat{\mathbb{Z}}^{\times}$ for the subgroup `unitIdeles` of finite idele units $\delta$ with $\delta$ and $\delta^{-1}$ integral at every height-one prime; the adeles carry the Borel $\sigma$-algebra `adeleBorel` and $\mathrm{GL}_3(\mathbb{A})$ its Borel $\sigma$-algebra. Fix a $\sigma$-algebra on $\widehat{\mathbb{Z}}^{\times}$ for which $u \mapsto \mathrm{finUnitIdele}(u) \in \mathbb{A}$ (the unit induced by the inclusion of the finite adeles) is measurable, and a finite measure $du$ on it. Let $\Phi \colon \mathbb{A}^3 \to \mathbb{C}$ be a product $\Phi(x) = \prod_{i} \Phi_i(x_i)$ of three functions each in `pureTensorSet`, i.e. of the form $x \mapsto g(x_\infty) h(x_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space and $h$ locally constant with compact support. Fix reals $a, b$ and a set $\Phi_0 \subseteq \mathrm{GL}_3(\mathbb{A})$ with $0 < a < b$ such that $\Phi_0$ is a fundamental domain for the range of $\mathrm{GL}_3(\mathbb{Q}) \to \mathrm{GL}_3(\mathbb{A})$ acting on the slab measure, the $\mathrm{GL}_3(\mathbb{A})$-Haar measure restricted to $\{g : \lVert \det g \rVert \in [a,b]\}$; let `domainMeasure` be its further restriction to $\Phi_0$. Assume $\mathrm{gauge3}\,\mathbb{Q} = \max(1, \mathrm{archGauge3} \cdot \mathrm{finGauge3})$ is measurable. Fix $S_g \subseteq \mathrm{GL}_3(\mathbb{A})$ of finite slab measure such that slab-almost every $x$ admits $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ with $\gamma x \in S_g$, a height function $\mathrm{ht}$ and $c_0 > 0$ with $c_0 \le \mathrm{ht}(g)$ on $S_g$, and constants $C_4, k$ with $\mathrm{gauge3}\,\mathbb{Q}(g) \le C_4\,\mathrm{ht}(g)^k$ for $g \in S_g$ in the determinant slab. Finally let $\varphi$ be continuous on $\mathrm{GL}_3(\mathbb{A})$, invariant under left translation by $\mathrm{GL}_3(\mathbb{Q})$, and of rapid decay on $S_g$: for each $N$ there is $C$ with $\lVert \varphi(g) \rVert \mathrm{ht}(g)^N \le C$ on $S_g$. Then, with $E(\sigma, g) = \mathrm{epstein}\,du\,\Phi\,\sigma\,g = \lVert \det g \rVert^{\sigma} \int_0^{\infty} t^{3\sigma} \int_{\widehat{\mathbb{Z}}^{\times}} \mathrm{latticeSum}\,\Phi\,t\,u\,g \; du \, \frac{dt}{t}$: first, for every $\sigma \in (1,2]$ the function $g \mapsto \varphi(g)\overline{\varphi(g)} E(\sigma, g)$ is integrable for `domainMeasure`; second, as $\sigma \to 1^{+}$ within $(1,\infty)$,
--   $$(\sigma - 1) \int \varphi \overline{\varphi} E(\sigma, \cdot) \longrightarrow \frac{du(\widehat{\mathbb{Z}}^{\times}) \int_{\mathbb{A}^3} \Phi}{3\,\mathrm{vol}\big(\prod_{i<3} B\big)} \int \varphi \overline{\varphi},$$
--   both integrals over `domainMeasure`, where the measure on $\mathbb{A}^3$ is the threefold product of the adelic additive Haar measure and $B$ is the adelic box `adelicBox`.
--
--   This is the analytic heart of the Rankin–Selberg unfolding for the degree-three Epstein zeta integral on $\mathrm{GL}_3$ over $\mathbb{Q}$: the integral has a simple pole at $\sigma = 1$ whose residue, paired against $|\varphi|^2$ on a determinant-slab fundamental domain, is a constant depending only on $\Phi$ and $du$ times the $L^2$-norm of $\varphi$. It feeds the construction of smoothing kernels and the associated spectral expansions in the $L^2$-theory of the slab used in the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
LanglandsTunnell.CubicInduction.AdelicEpstein.integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (hmeas : @Measurable (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (AdeleRing (𝓞 ℚ) ℚ) _
      (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u => ((finUnitIdele u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)))
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hΦ : ∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          Φ = fun x => ∏ i, Φc i (x i))
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : SlabL2.IsSlabDomain a b Φ₀)
    (hgm : Measurable (gauge3 ℚ))
    (Sg : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ᵐ x ∂(SlabL2.slabMeasure a b), ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Sg)
    (hSfin : SlabL2.slabMeasure a b Sg < ⊤)
    (ht : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀) (hfloor : ∀ g ∈ Sg, c₀ ≤ ht g)
    (hgauge : ∃ (C₄ : ℝ) (k : ℕ), ∀ g ∈ Sg, g ∈ SlabL2.ideleNormDetSlab a b → gauge3 ℚ g ≤ C₄ * ht g ^ k)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ Sg, ‖φ g‖ * ht g ^ N ≤ C) :
    (∀ σ ∈ Set.Ioc (1 : ℝ) 2,
        Integrable (fun g => φ g * starRingEnd ℂ (φ g) * epstein du Φ σ g) (SlabL2.domainMeasure a b Φ₀)) ∧
      Filter.Tendsto
        (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) *
          ∫ g, φ g * starRingEnd ℂ (φ g) * epstein du Φ σ g ∂(SlabL2.domainMeasure a b Φ₀))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds
          ((letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
            (((du Set.univ).toReal : ℂ) *
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
            (3 * (((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ)))) *
            ∫ g, φ g * starRingEnd ℂ (φ g) ∂(SlabL2.domainMeasure a b Φ₀))) := by sorry
