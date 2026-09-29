-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
-- name    : LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b2aa6e31-021f-5415-8c88-a7dc896f7bda
-- title:
--   Uniform exponent θ₀>1/2 for ray decay of GL₃ Whittaker integrals
-- statement:
--   Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $\|\omega(z)\|=1$ for all $z$, and let $f$ be a continuous complex function on $GL_3(\mathbb{A}_\mathbb{Q})$ such that: $f(\gamma g)=f(g)$ for $\gamma \in GL_3(\mathbb{Q})$ embedded diagonally; $f(zg)=\omega(z)f(g)$ for central scalars $z$; $f$ is slowly increasing for the gauge `gauge3`, i.e. $\|f(g)\|\le C\,\mathrm{gauge3}(g)^N$ for some $C,N$; the two double integrals of $f$ over the unipotent radicals `radicalP21` and `radicalP12` vanish at every $g$, the integration being against the adelic additive Haar measure conditioned on the box `AdelicBox.adelicBox` (the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) _`); for every prime $p$ outside a given finite set $S$, $f$ is right invariant under the image of `localMaximalCompact3` at $p$ (matrices whose entries and inverse entries have valuation $\le 1$); at every finite place $v$ some open subgroup of $GL_3(\mathbb{Q}_v)$ acts trivially on the right; $e \mapsto f(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on invertible real matrices for each $g$; and the right translates $f(\cdot\,k)$ for $k$ trivial at all finite places and orthogonal at the archimedean place lie in the span of one finite set of functions. Let $c : \mathrm{Fin}\,n \to \mathbb{C}$ and $t : \mathrm{Fin}\,n \to GL_3(\mathbb{A}_\mathbb{Q})$ with each $t_i$ trivial at the archimedean place, and assume the combination $x \mapsto \sum_i c_i f(x t_i)$ is centre-finite, i.e. each of `casimir1`, `casimir2`, `casimir3` (built from the archimedean derivations `archDeriv`) satisfies a monic polynomial relation annihilating it. Then there is a single $\theta_0 > 1/2$ such that for every $u$ in the $\mathbb{C}$-span of the functions obtained by applying a word of iterated operators $\mathrm{archDeriv}\,i\,j$ to $g \mapsto \sum_i c_i f(ght_i)$, $h \in GL_3(\mathbb{A}_\mathbb{Q})$ arbitrary: for every $y_2>0$ there is $C$ with $\|W_u(\mathrm{diag}(y_1y_2,y_2,1))\| \le C y_1^{\theta_0}$ for $0<y_1\le 1$, and for every $y_1>0$ there is $C$ with $\|W_u(\mathrm{diag}(y_1y_2,y_2,1))\| \le C y_2^{\theta_0}$ for $0<y_2\le 1$; here $W_u$ is `whittaker3` for the same pins and the standard character `psiQ`, namely the triple integral of $u(\mathrm{upperUnipotent3}(x,y,z)\,g)\,\psi(-(x+y))$, and the diagonal argument is the archimedean lift `archRealLift3` of $\mathrm{diag}(y_1y_2,y_2,1)$.
--
--   This is the ray-by-ray decay estimate for Whittaker coefficients of a centre-finite combination of right translates of a $GL_3$ cusp form, with the exponent $\theta_0>1/2$ chosen uniformly in the member of the derived span and in both rays. It feeds the construction of a nonvanishing Whittaker coefficient together with the corresponding block bound in the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant.lean

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
LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant
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
    ∃ θ₀ : ℝ, 1 / 2 < θ₀ ∧ ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₁ ^ θ₀) ∧
      (∀ y₁ : ℝ, 0 < y₁ → ∃ C : ℝ, ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0))‖ ≤ C * y₂ ^ θ₀) := by sorry
