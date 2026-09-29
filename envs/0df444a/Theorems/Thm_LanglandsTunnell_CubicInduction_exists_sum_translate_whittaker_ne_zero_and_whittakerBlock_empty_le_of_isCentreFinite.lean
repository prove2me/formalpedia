-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite
-- name    : LanglandsTunnell.CubicInduction.exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/2c781d48-3f44-524a-9969-41393ab5ab87
-- title:
--   Translate combination with non-zero Whittaker coefficient and bounded block
-- statement:
--   Fix a finite set $S$ of finite places of $\mathbb{Q}$, a homomorphism $\omega$ from the idele units to $\mathbb{C}^\times$ with $|\omega(z)|=1$ throughout, and families of complex numbers $\lambda_1,\lambda_2$ indexed by the finite places. Let $f:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, invariant under left translation by $\mathrm{GL}_3(\mathbb{Q})$, of central character $\omega$ (i.e. $f(zg)=\omega(z)f(g)$ for scalar adelic matrices $z$), of moderate growth in the sense that $\|f(g)\|\le C\,\mathrm{gauge}_3(g)^N$ for some $C,N$ on all of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$, and cuspidal along both maximal unipotent radicals: for every $g$ the double integral of $f\bigl(u\,g\bigr)$ vanishes, where $u$ runs over the matrices $\begin{pmatrix}1&0&x\\0&1&y\\0&0&1\end{pmatrix}$, respectively $\begin{pmatrix}1&x&y\\0&1&0\\0&0&1\end{pmatrix}$, with $x,y$ integrated against the probability measure obtained by conditioning adelic additive Haar measure to the adelic box (a fundamental domain at infinity times the integral finite adeles). Assume further: at every $p\notin S$, $f$ is right invariant under the image of the local maximal compact subgroup (entries of the matrix and of its inverse of valuation $\le 1$) and is a coset eigenfunction, with eigenvalue $\lambda_1(p)$ for $\mathrm{diag}(\varpi_p,1,1)$ and $\lambda_2(p)$ for $\mathrm{diag}(\varpi_p,\varpi_p,1)$, meaning that $\sum_i f(g\,r_i)=\lambda\,f(g)$ for every finite system of coset representatives of the corresponding double coset; at every finite $v$ some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ fixes $f$ on the right; $e\mapsto f(g\cdot\mathrm{archRealLift}_3(e))$ is smooth on invertible real $3\times 3$ matrices for each $g$; the right translates $f(\,\cdot\,k)$, for $k$ trivial at all finite places with archimedean component satisfying $k^{\mathsf T}k=1$, lie in the span of a single finite set of functions; each of the three operators $\mathrm{casimir}_1,\mathrm{casimir}_2,\mathrm{casimir}_3$ satisfies a monic polynomial relation when applied iteratively to $f$; and $f\ne 0$. The conclusion asserts the existence of $n$, coefficients $c:\mathrm{Fin}\,n\to\mathbb{C}$ and elements $t_i\in\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$, each with trivial archimedean component and trivial component at every $p\notin S$, such that for $v(x)=\sum_i c_i f(x t_i)$ the following hold. First, the Whittaker integral $\int\!\!\int\!\!\int v\bigl(u(x,y,z)g\bigr)\psi_{\mathbb{Q}}(-(x+y))$, taken against the box measure in each variable and with $\psi_{\mathbb{Q}}$ the standard additive character of $\mathbb{A}_\mathbb{Q}$, is non-zero at some $g$ whose class modulo the orbit relation of the adelic upper unipotent subgroup lies in the zeroth shell for $\varnothing$, that is, the $p$-component of the chosen representative is an upper unipotent matrix times an element of the local maximal compact subgroup at every finite $p$. Second, there is $\Phi:\mathbb{A}_\mathbb{Q}^3\to\mathbb{C}$ of the form $\Phi(x)=\prod_i\Phi_i(x_i)$ with each $\Phi_i$ a pure tensor (Schwartz at infinity times a locally constant compactly supported function on the finite adeles) which is factorizable and standard outside $\varnothing$, with $\Phi$ taking non-negative real values and $\int_{\mathbb{A}^3}\Phi>0$ for the product adelic Haar measure, together with a finite $C\in\mathbb{R}_{\ge 0}^{\infty}$ such that for every real $\sigma$ with $1<\sigma\le 2$ the block quantity $\int^{-}_{q\in\text{zeroth shell}}\|W_v(q)\|^2\,\|\Phi(\text{third row of }q)\|\,\|\det q\|_{\mathbb{A}}^{\sigma}$, against the quotient measure induced by Haar measure, is at most $C$.
--
--   This is the analytic estimate on Whittaker blocks for cusp functions on $\mathrm{GL}_3$ over $\mathbb{Q}$ in the style of Jacquet–Piatetski-Shapiro–Shalika, in the edition where finiteness under the three Casimir-type operators at the archimedean place is assumed rather than derived. It is the input to [`LanglandsTunnell.CubicInduction.exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite`](thm.html#LanglandsTunnell.CubicInduction.exists_sum_translate_ne_zero_and_whittakerBlock_le_of_isCentreFinite), within the cubic-induction route to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite.lean

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

theorem
LanglandsTunnell.CubicInduction.exists_sum_translate_whittaker_ne_zero_and_whittakerBlock_empty_le_of_isCentreFinite
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
      (∃ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (Quotient.mk'' g :
            MulAction.orbitRel.Quotient ↥WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ)) ∈
            WhittakerBlock.zerothShell ∅ ∧
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) g ≠ 0) ∧
      ∃ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) ∅ g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) ∧
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
          WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * f (x * t i)) Φ σ ∅ ≤ C := by sorry
