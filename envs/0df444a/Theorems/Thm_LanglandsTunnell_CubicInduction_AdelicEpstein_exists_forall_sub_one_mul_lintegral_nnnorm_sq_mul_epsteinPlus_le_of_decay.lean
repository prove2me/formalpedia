-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
-- name    : LanglandsTunnell.CubicInduction.AdelicEpstein.exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/1f3f9237-0836-522e-aa6e-4c27bc4930bf
-- title:
--   Uniform simple-pole bound for the adelic Epstein pairing on a slab
-- statement:
--   Fix a finite measure $du$ on the group $\widehat{\mathbb Z}^\times$ of finite unit ideles of $\mathbb Q$ (the units $\delta$ of the finite adele ring with both $\delta$ and $\delta^{-1}$ integral at every height-one prime of $\mathcal O_{\mathbb Q}$), a function $\Phi \colon \mathbb A_{\mathbb Q}^{3} \to \mathbb C$, reals $M, R_0$ with $0 \le R_0$, and a natural number $N > 0$, such that $\|\Phi(x)\| \le M$ for all $x$, and such that whenever $\Phi(x) \neq 0$ one has $\|(x_i)_\infty\| \le R_0$ at the infinite place of $\mathbb Q$ for every $i$, and $N \cdot (x_i)_{\mathrm{fin}}$ lies in the valuation ring at every height-one prime $w$, for every $i$. Fix reals $a, b$ and a set $\Phi_0 \subseteq \mathrm{GL}_3(\mathbb A_{\mathbb Q})$ with `IsSlabDomain a b Φ₀`, i.e. $0 < a < b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb Q)$ under `globalPointsGL` with respect to the slab measure, namely adelic Haar measure on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ restricted to $\{g : \|\det g\| \in [a,b]\}$, the idele norm being `TateGlobal.ideleNorm`. Assume the gauge `gauge3 ℚ` $= \max(1, \text{archGauge3} \cdot \text{finGauge3})$ is measurable. Fix a set $S_g$ of finite slab measure such that slab-almost every $x$ admits $\gamma \in \mathrm{GL}_3(\mathbb Q)$ with $\gamma x \in S_g$, and a continuous $\varphi \colon \mathrm{GL}_3(\mathbb A_{\mathbb Q}) \to \mathbb C$ invariant under left translation by global points, satisfying rapid decay on $S_g$: for each $K \in \mathbb N$ there is $C$ with $\|\varphi(g)\| \cdot \mathrm{gauge3}(g)^K \le C$ for all $g \in S_g$. The conclusion is that there exists $C_2 \in [0,\infty]$ with $C_2 \neq \infty$ such that for every $\sigma \in (1,2]$, $$(\sigma - 1)\int^{-}_{\Phi_0} \|\varphi(g)\|^{2}\, \mathrm{epsteinPlus}(du, \Phi, \sigma, g)\, dg \le C_2,$$ the lower Lebesgue integral being taken against the slab measure restricted to $\Phi_0$, and $\mathrm{epsteinPlus}(du,\Phi,\sigma,g)$ being the $[0,\infty]$-valued quantity $\|\det g\|^{\sigma} \int_0^{\infty} t^{3\sigma} \int_{\widehat{\mathbb Z}^\times} \sum_{\xi \in \mathbb Q^3 \setminus \{0\}} \|\Phi(\mathrm{point}(t,u,g,\xi))\| \, du \, \frac{dt}{t}$.
--
--   This is the uniform-in-$\sigma$ bound on $(1,2]$ expressing the simple pole of the degenerate Eisenstein (Epstein) integral attached to $\Phi$ when paired with the square of a rapidly decreasing automorphic function on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ over a determinant slab. It feeds the bound `exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant` on torus integrals of Whittaker functions, and rests on the pointwise estimate `epsteinPlus_le_mul_gauge3_rpow_div_sub_one` together with the left $\mathrm{GL}_3(\mathbb Q)$-invariance of `epsteinPlus`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ : ℝ) (hR₀ : 0 ≤ R₀) (N : ℕ) (hN : 0 < N)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (hfin : ∀ x, Φ x ≠ 0 → ∀ (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x i).2) w ∈ w.adicCompletionIntegers ℚ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : SlabL2.IsSlabDomain a b Φ₀)
    (hgm : Measurable (gauge3 ℚ))
    (Sg : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ᵐ x ∂(SlabL2.slabMeasure a b), ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Sg)
    (hSfin : SlabL2.slabMeasure a b Sg < ⊤)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hdecay : ∀ K : ℕ, ∃ C : ℝ, ∀ g ∈ Sg, ‖φ g‖ * gauge3 ℚ g ^ K ≤ C) :
    ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧ ∀ σ ∈ Set.Ioc (1 : ℝ) 2,
      ENNReal.ofReal (σ - 1) *
          ∫⁻ g, (‖φ g‖₊ : ℝ≥0∞) ^ 2 * AdelicEpstein.epsteinPlus du Φ σ g ∂(SlabL2.domainMeasure a b Φ₀) ≤ C₂ := by sorry
