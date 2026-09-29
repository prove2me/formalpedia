-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
-- name    : LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/3012f835-9a96-5aef-84df-d10d8bc42950
-- title:
--   Simple-pole bound for torus mean squares of GL₃ Whittaker coefficients
-- statement:
--   Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ all of whose values have absolute value $1$, and let $u : GL_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be continuous, invariant under left translation by the image of $GL_3(\mathbb{Q})$ under `globalPointsGL`, and satisfying $u(zg) = \omega(z)\,u(g)$ for central scalars $z$. Assume $u$ is cuspidal along both maximal parabolics in the sense that for all $g$ the double integrals of $u(\,\mathrm{upperUnipotent3}\,0\,y\,x \cdot g)$ and of $u(\,\mathrm{upperUnipotent3}\,x\,0\,y \cdot g)$ vanish, the integrations being against the Haar measure of $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box; that for $p$ outside a finite set $S$ of finite places $u$ is right invariant under the image of `localMaximalCompact3` in $GL_3(\mathbb{A}_{\mathbb{Q}})$, and at every finite place under some open subgroup; that $e \mapsto u(g\cdot \mathrm{archRealLift3}\,e)$ is smooth on invertible real matrices for each $g$; that the right translates $g \mapsto u(gk)$, for $k$ with trivial finite components and orthogonal archimedean component, span a finite-dimensional space; and, for a fixed $N$, that every word of archimedean derivatives `archDeriv` applied to $u$ is continuous and bounded by a constant times $\mathrm{gauge3}(g)^N$. Then for every compact $B \subseteq GL_3(\mathbb{A}_{\mathbb{Q}})$ and every $b_0 > 1$ there are $\Phi : \mathbb{A}_{\mathbb{Q}}^3 \to \mathbb{C}$ and $\varphi_0 > 0$ such that $\varphi_0 \le \|\Phi(\text{third row of } \mathrm{archRealLift3}(\mathrm{diag}\,a)\cdot k)\|$ for all $k \in B$ and all $a$ with positive entries and $b_0^{-1} \le a_2 \le b_0$, and a constant $C'$ with $$\int_{B}\int_{(0,\infty)^3} \|W(\mathrm{archRealLift3}(\mathrm{diag}\,a)\cdot k)\|^2\,\|\Phi(\cdots)\|\, a_0^{\sigma-3}a_1^{\sigma-1}a_2^{\sigma+1}\,da\,dk \le \frac{C'}{\sigma-1}$$ as an inequality of lower Lebesgue integrals in $\overline{\mathbb{R}}_{\ge 0}$, for every $\sigma \in (1,2]$; here $W = \mathrm{whittaker3}$ is the triple unipotent integral of $u$ against the standard additive character `psiQ`, taken with the same conditioned measure, and $dk$ is the Haar measure `adelicGLHaar`.
--
--   This is the mean-square input obtained by Rankin–Selberg unfolding of a $GL_3$ cusp form against a mirabolic Epstein–Eisenstein series: the torus slices of $|W_u|^2$ over a compact set, weighted by $\Phi$ and by the exponents $\sigma-3$, $\sigma-1$, $\sigma+1$, have at worst a simple pole as $\sigma \downarrow 1$. It supplies the quantitative hypothesis used in the analysis of ray orders of archimedean derivatives of Whittaker coefficients under the Casimir relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem
LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous u)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) u)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, u (g * localToAdelic3 v k) = u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (N : ℕ) (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hB : IsCompact B) (b₀ : ℝ) (hb₀ : 1 < b₀) :
    ∃ (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (φ₀ : ℝ), 0 < φ₀ ∧
      (∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
        φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                      AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖) ∧
      ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
      (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
        ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
            (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                  NumberField.StandardAddChar.psiQ u
                  (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                  AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
          ENNReal.ofReal (C' / (σ - 1))) := by sorry
