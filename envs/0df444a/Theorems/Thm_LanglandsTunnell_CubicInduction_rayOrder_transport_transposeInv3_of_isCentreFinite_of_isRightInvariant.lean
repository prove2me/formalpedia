-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
-- name    : LanglandsTunnell.CubicInduction.rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b00c17e7-b4d2-5ef1-b0e5-d7fa50faa072
-- title:
--   Transport of the GL₃ cusp package under g↦(g^{mathsf T})⁻¹
-- statement:
--   Let $\omega$ be a homomorphism from the idele units of $\mathbb{Q}$ to $\mathbb{C}^\times$ with all values of absolute value $1$, and let $f$ be a continuous function on $GL_3$ of the adeles of $\mathbb{Q}$ which is left invariant under the image of $GL_3(\mathbb{Q})$, satisfies $f(zg)=\omega(z)f(g)$ for central scalars $z$, is slowly increasing with respect to the gauge $\max(1,\text{arch gauge}\cdot\text{finite gauge})$, and is cuspidal along both $P_{21}$ and $P_{12}$, i.e. the double integrals of $f$ over the two unipotent radicals $(x,y)\mapsto\mathrm{upperUnipotent3}\,0\,y\,x$ and $(x,y)\mapsto\mathrm{upperUnipotent3}\,x\,0\,y$, taken against adelic Haar measure conditioned to the standard adelic box, vanish at every $g$. Assume further: $f$ is right invariant under the images of the local integral subgroups $\mathrm{localMaximalCompact3}$ outside a finite set $S$ of finite places; at every finite place some open subgroup acts trivially on the right; $f$ is archimedean smooth in the sense of `IsArchSmooth3`; and the right translates $g\mapsto f(gk)$, for $k$ with trivial finite components and orthogonal archimedean component, span a finite-dimensional space. Let $c:\mathrm{Fin}\,n\to\mathbb{C}$ and $t:\mathrm{Fin}\,n\to GL_3(\mathbb{A})$ with $\mathrm{archComponent3}(t_i)=1$, and suppose $v=\sum_i c_i f(\cdot\,t_i)$ is centre-finite, i.e. each of the operators `casimir1`, `casimir2`, `casimir3` annihilates $v$ through a monic polynomial in its iterates. Writing $\iota(g)=((g^{-1})^{\mathsf T})$ for `transposeInv3`, the conclusion is the conjunction: $f\circ\iota$ is continuous, left $GL_3(\mathbb{Q})$-invariant, transforms under the centre by $\omega^{-1}$ (whose values again have absolute value $1$), is slowly increasing for the same gauge, is cuspidal along $P_{21}$ and along $P_{12}$ for the same pins, is right invariant under the local integral subgroups outside $S$ and under an open subgroup at each finite place, is archimedean smooth, and has finite-dimensional span of its orthogonal translates; moreover $\mathrm{archComponent3}(\iota(t_i))=1$ for all $i$, the combination $x\mapsto\sum_i c_i f(\iota(x\,\iota(t_i)))$ is centre-finite, and for every $h$ there exists $h'$ such that each $u$ in the complex span of the functions obtained by applying words of archimedean derivatives `archDeriv` to $g\mapsto\sum_i c_i f(ghT_i)$ (over all words and all $h$) has $u\circ\iota$ in the corresponding span for the transported combination, and for all $y_1,y_2>0$ the Whittaker integral of $u$ against the standard additive character $\psi_{\mathbb{Q}}$ at $\mathrm{diag}(y_1y_2,y_2,1)_\infty h$ and that of $u\circ\iota$ at $\mathrm{diag}(y_2y_1,y_1,1)_\infty h'$ have equal absolute values.
--
--   This records the transport of the whole $GL_3$ cusp-form package, of centre-finiteness for a finite combination of right translates, and of Whittaker values along the two-parameter torus ray, under the outer involution $g\mapsto(g^{\mathsf T})^{-1}$, which exchanges the two maximal parabolic subgroups and inverts the central character. It feeds the ray estimate `exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant`, where the symmetry between the two torus coordinates is used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

theorem
LanglandsTunnell.CubicInduction.rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i)) :

    (Continuous fun g => f (transposeInv3 g)) ∧
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (transposeInv3 (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g)) = f (transposeInv3 g)) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (transposeInv3 (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) = (ω⁻¹ z : ℂ) * f (transposeInv3 g)) ∧
    (∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω⁻¹ z : ℂ)‖ = 1) ∧
    IsModerateGrowth3 ℚ (fun g => f (transposeInv3 g)) ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) (fun g => f (transposeInv3 g)) ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) (fun g => f (transposeInv3 g)) ∧
    (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (fun g => f (transposeInv3 g))) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (transposeInv3 (g * localToAdelic3 v k)) = f (transposeInv3 g)) ∧
    WhittakerBlock.IsArchSmooth3 (fun g => f (transposeInv3 g)) ∧
    (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (transposeInv3 (g * k))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    (∀ i, archComponent3 (𝓞 ℚ) ℚ (transposeInv3 (t i)) = 1) ∧

    IsCentreFinite (fun x => ∑ i, c i * f (transposeInv3 (x * transposeInv3 (t i)))) ∧

    (∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ h' : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (fun g => u (transposeInv3 g)) ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ |
        ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (transposeInv3 (g * h * transposeInv3 (t i)))) w} ∧
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * h)‖ =
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => u (transposeInv3 g))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₂ * y₁, y₁, 1] i else 0) * h')‖) := by sorry
