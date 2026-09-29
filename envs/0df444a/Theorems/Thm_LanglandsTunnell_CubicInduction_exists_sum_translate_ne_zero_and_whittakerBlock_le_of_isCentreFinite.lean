-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
-- name    : LanglandsTunnell.CubicInduction.exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/4b4f8b98-c86a-5aba-a216-4302b6fa0cc7
-- title:
--   Bounded Whittaker block for a centre-finite cusp form on GL₃
-- statement:
--   Fix a finite set $S$ of finite places of $\mathbb{Q}$, a character $\omega$ of the idele units with $|\omega(z)|=1$ throughout, and two families of complex scalars $\lambda_1,\lambda_2$ indexed by the finite places. Let $f:\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_3(\mathbb{Q})$, with $f(zg)=\omega(z)f(g)$ for central scalars $z$, of moderate growth in the sense that $\|f(g)\|\le C\,\mathrm{gauge}_3(g)^N$ for some $C,N$, and cuspidal along both maximal parabolics: for all $g$ the double integrals of $f$ over the unipotent radicals $u(0,y,x)$ and $u(x,0,y)$ vanish, the adelic variables being integrated against Haar measure on $\mathbb{A}_\mathbb{Q}$ conditioned to the adelic box. Assume further that at each $p\notin S$ the function $f$ is right invariant under the image of the local maximal compact subgroup (entries and inverse entries of valuation $\le 1$) and is a coset eigenfunction with eigenvalues $\lambda_1(p),\lambda_2(p)$ for the generators $\mathrm{diag}(\varpi,1,1)$ and $\mathrm{diag}(\varpi,\varpi,1)$, i.e. $\sum_i f(g\,r_i)=\lambda\,f(g)$ for every finite system of representatives of the relevant double coset modulo the compact; that at every finite place $f$ is right invariant under some open subgroup; that $e\mapsto f(g\cdot e)$ is $C^\infty$ on invertible real $3\times3$ matrices for each $g$; that the right translates $g\mapsto f(gk)$, for $k$ trivial at all finite places and with archimedean component satisfying $k^{\mathsf T}k=1$, lie in the span of a single finite set of functions; that $f$ is annihilated by a monic polynomial in each of the three archimedean Casimir-type operators $\mathrm{casimir}_1,\mathrm{casimir}_2,\mathrm{casimir}_3$; and that $f\neq0$. Then there are $n\in\mathbb{N}$, scalars $c_i$ and elements $t_i\in\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$, each trivial at the archimedean place and at every $p\notin S$, such that $\varphi_0:=\sum_i c_i\,f(\,\cdot\,t_i)$ is non-zero, together with a function $\Phi$ on $\mathbb{A}_\mathbb{Q}^3$ of the form $\Phi(x)=\prod_{i}\Phi_i(x_i)$ with each $\Phi_i$ a pure tensor (a Schwartz function at infinity times a locally constant compactly supported function on the finite adeles) and equal to the indicator of the set of adeles integral outside $S$ times a product of archimedean factors and of factors at the places in $S$, with $\Phi$ real-valued and non-negative and with positive integral against the product of adelic Haar measures, and a finite $C\in\mathbb{R}_{\ge0}^{\infty}$ such that for every $\sigma\in(1,2]$ the Whittaker block of $\varphi_0$ against $\Phi$ — the lower integral over the zeroth shell of the quotient of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ by the unipotent subgroup, with respect to the quotient Haar measure, of $\|W_{\varphi_0}(q)\|^2\,\|\Phi(\text{third row of }q)\|\,\|\det q\|^{\sigma}$, the Whittaker coefficient being taken against the standard additive character $\psi_\mathbb{Q}$ — is at most $C$.
--
--   This is the boundedness statement for the Whittaker block attached to a cuspidal function on $\mathrm{GL}_3$ over the rational adeles, in the edition in which finiteness under the archimedean Casimir operators is assumed rather than deduced; it packages the Rankin–Selberg type convergence estimate for $\int |W|^2 |\Phi| \|\det\|^{\sigma}$ uniformly for $1<\sigma\le 2$. It is used to produce a non-zero $L^2$ inner product for a translate of the form, in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open scoped ENNReal

theorem LanglandsTunnell.CubicInduction.exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hc : Continuous f)
    (_haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (_hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (_hmg : IsModerateGrowth3 ℚ f)
    (_hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) f (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) f (lam2 p))
    (_hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (_hsa : WhittakerBlock.IsArchSmooth3 f)
    (_hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (_hzf : WhittakerBlock.IsCentreFinite f)
    (_hf : f ≠ 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1 ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) ∧
      (fun x => ∑ i, c i * f (x * t i)) ≠ 0 ∧
      ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) Φ σ S ≤ C := by sorry
