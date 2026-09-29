-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff
-- name    : LanglandsTunnell.CubicInduction.smoothingModule_expansion_leadingCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/0f6f3785-ee03-531f-86c6-0d75f052d541
-- title:
--   Smoothing module on GL₃: leading-coefficient functional and its properties
-- statement:
--   Throughout, $G$ denotes `AdelicGL 3 (𝓞 ℚ) ℚ`, the group $\mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$, and the carrier pins are `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`: the empty fundamental domain, trivial level subgroups, unit uniformisers, full central subgroup, adelic Haar measure on $\mathrm{GL}_2$ of the adeles, and for the additive measure the adelic additive Haar measure conditioned on the adelic box `AdelicBox.adelicBox ℚ` (the product of a fundamental domain for the lattice at the infinite places with the integral finite adeles). Only the additive measure $\nu$ of these pins enters, through `whittaker3 pins NumberField.StandardAddChar.psiQ Φ g` $= \int\!\!\int\!\!\int \Phi(\mathrm{upperUnipotent3}\, x\,y\,z \cdot g)\,\psi_{\mathbb{Q}}(-(x+y))\,d\nu\,d\nu\,d\nu$, where `upperUnipotent3 x y z` is the upper triangular unipotent matrix with entries $x$, $y$, $z$ and $\psi_{\mathbb{Q}}$ is the standard additive character of $\mathbb{A}_\mathbb{Q}$. For a real matrix $e$, [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) is the element of $G$ obtained from the archimedean inclusion of $e$ when that matrix is invertible, and $1$ otherwise; `orth3` is the set of $k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ with $k^{\mathsf T}k = 1$; and for $i,j \in \{0,1,2\}$, `WhittakerBlock.archDeriv i j φ (g)` is the derivative at $s=0$ of $s \mapsto φ(g\cdot$ `archRealLift3`$(I + sE_{ij}))$.
--
--   The data are: a homomorphism $\omega : (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$ with $\|\omega(z)\| = 1$ for all $z$ (`hω`); a function $f : G \to \mathbb{C}$ which is continuous (`hc`), invariant under left translation by the rational points $\mathrm{GL}_3(\mathbb{Q})$ (`haut`), transforms by $\omega$ under the central adelic scalars (`hcen`), is of moderate growth in the sense that $\|f(g)\| \le C\,\mathrm{gauge}_3(g)^N$ for some $C$ and $N$ and all $g$ (`hmg`), is cuspidal along the two maximal parabolics in the sense that the double $\nu$-integrals of $f$ over the unipotent radicals `radicalP21` and `radicalP12` vanish at every $g$ (`hP21`, `hP12`), is archimedean smooth in the sense that $e \mapsto f(g\cdot$ `archRealLift3` $e)$ is $C^\infty$ on the set of matrices of nonzero determinant, for every $g$ (`hsa`), and has finitely many right translates modulo linear combinations: there is a finite set $s$ of functions on $G$ such that $g \mapsto f(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ that is trivial at all finite places and orthogonal at the infinite places (`hKf`).
--
--   Further data: $n \in \mathbb{N}$, scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$ and elements $t : \mathrm{Fin}\,n \to G$ with $t_i$ trivial at the archimedean places (`ht`), such that $x \mapsto \sum_i c_i f(x t_i)$ is centre-finite (`hz`), i.e. annihilated by a monic polynomial in each of the three operators `casimir1`, `casimir2`, `casimir3` built from the `archDeriv` operators. A function $u : G \to \mathbb{C}$ is assumed to lie in the $\mathbb{C}$-span of the functions obtained by applying a word of operators `archDeriv` to $g \mapsto \sum_i c_i f(g h t_i)$ for some $h \in G$ (`hu`).
--
--   Finally, the expansion data: $m, J \in \mathbb{N}$, an injective $e : \mathrm{Fin}\,m \to \mathbb{C}$ (`he`), coefficients $a_{ij} : \mathbb{R} \to G \to \mathbb{C}$ jointly continuous on $\{(y_2,g) : y_2 > 0\}$ (`hcont`), a real $\tau$ with $1/2 < \tau$ (`hτ`), and the hypothesis `hexp` that for every compact $K \subseteq G$ and every $b \ge 1$ there is $C$ with
--   $$\Big\| W_u\big(\mathrm{diag}(y_1y_2,y_2,1)\,k\big) - \sum_{i<m}\sum_{j<J} a_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j \Big\| \le C\,y_1^{\tau}$$
--   for all $k \in K$, all $y_2$ with $b^{-1} \le y_2 \le b$ and all $y_1$ with $0 < y_1 \le 1$, where $W_u =$ `whittaker3` of $u$ and $\mathrm{diag}(y_1y_2,y_2,1)$ means its image under `archRealLift3`. Lastly an index $i_0 \in \mathrm{Fin}\,m$ with $\mathrm{Re}(e_{i_0}) = 1/2$ (`hD`).
--
--   Two objects are formed from these data. First, $M$ is the $\mathbb{C}$-span of the image of the admissible smoothing kernels under $\varphi \mapsto$ `smoothingOperator` $\varphi\,u$, where `smoothingOperator` $\varphi\,u\,(x) = \int \varphi(g)\,u(xg)\,dg$ against adelic Haar measure on $G$, and where $\varphi$ is admissible when `IsSmoothingKernel φ` holds — that is, $\varphi(g) = \alpha(\mathrm{archEntries}\,g)$ times the indicator of $\{x :$ `componentAt3` $p\,x \in K'_p$ for all $p\}$, for some smooth compactly supported $\alpha$ whose support lies in the matrices of nonzero determinant and some open compact subgroups $K'_p$ equal to `localMaximalCompact3` for all but finitely many $p$ — and when in addition there is a finite set $S$ of functions whose span contains $g \mapsto \varphi(k^{-1}g)$ for every $k$ trivial at all finite places with archimedean component in `orth3`. Second, the leading-coefficient functional $A$ assigns to $w : G \to \mathbb{C}$, $y_2 \in \mathbb{R}$ and $k \in G$ the value $b_{i_0,0}(y_2,k)$ for a classically chosen family $b$, provided $y_2 > 0$, $J > 0$, and there exists a family $b_{ij} : \mathbb{R} \to G \to \mathbb{C}$ jointly continuous on $\{y_2 > 0\}$ satisfying the displayed expansion bound with $W_w$ in place of $W_u$, the same exponents $e_i$, the same $J$ and the same $\tau$, uniformly for $k$ in compacts and $y_2$ in $[bd^{-1},bd]$ for each $bd \ge 1$; and the value $0$ otherwise.
--
--   The conclusion is the conjunction of five assertions.
--
--   (1) Right translation stability and equivariance: for every $w \in M$ and every $k \in G$ with `componentAt3` $p\,k = 1$ for all finite places $p$ and `archComponent3` $k \in$ `orth3`, the function $g \mapsto w(gk)$ again lies in $M$, and for all $y_2 \in \mathbb{R}$ and $k' \in G$ one has $A(g \mapsto w(gk))(y_2,k') = A(w)(y_2,k'k)$.
--
--   (2) Linearity: for every $z \in \mathbb{C}$, all $w_1, w_2 \in M$ and all $y_2 \in \mathbb{R}$, $k \in G$, $A(z\,w_1 + w_2)(y_2,k) = z\,A(w_1)(y_2,k) + A(w_2)(y_2,k)$.
--
--   (3) Existence of an expansion with prescribed leading coefficient: for every $w \in M$ there is a family $b_{ij} : \mathbb{R} \to G \to \mathbb{C}$ ($i < m$, $j < J$) such that each $b_{ij}$ is jointly continuous on $\{(y_2,g) : y_2 > 0\}$; for the index $j \in \mathrm{Fin}\,J$ with $(j : \mathbb{N}) = 0$ one has $b_{i_0,j}(y_2,k) = A(w)(y_2,k)$ for all $y_2 > 0$ and all $k$; and for every compact $K \subseteq G$ and every $bd \ge 1$ there is $C$ with $\big\| W_w(\mathrm{diag}(y_1y_2,y_2,1)k) - \sum_{i<m}\sum_{j<J} b_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^j \big\| \le C\,y_1^{\tau}$ for all $k \in K$, all $bd^{-1} \le y_2 \le bd$ and all $0 < y_1 \le 1$.
--
--   (4) Differentiability along the nine elementary flows: for every $w \in M$, all $i, j \in \mathrm{Fin}\,3$, every $y_2 \in \mathbb{R}$ and every $k \in G$, the function $s \mapsto A(w)(y_2,\;k\cdot$ `archRealLift3`$(I + sE_{ij}))$ has derivative $A(\mathrm{archDeriv}\,i\,j\,w)(y_2,k)$ at $s = 0$.
--
--   (5) Differentiability along the three rotation planes: for every $w \in M$, all $c_1 < c_2$ in $\mathrm{Fin}\,3$, every $y_2 \in \mathbb{R}$ and every $k \in G$, the function $s \mapsto A(w)(y_2,\;k\cdot$ `archRealLift3` $R_{c_1c_2}(s))$, where $R_{c_1c_2}(s)$ has entries $\cos s$ at $(c_1,c_1)$ and $(c_2,c_2)$, $-\sin s$ at $(c_1,c_2)$, $\sin s$ at $(c_2,c_1)$, and agrees with the identity elsewhere, has derivative $A(\mathrm{archDeriv}\,c_2\,c_1\,w)(y_2,k) - A(\mathrm{archDeriv}\,c_1\,c_2\,w)(y_2,k)$ at $s = 0$.
--
--   This is the assembly statement for the module of smoothings of a centre-finite, cuspidal, moderate-growth vector $u$ on $\mathrm{GL}_3$ over $\mathbb{Q}$ and for the functional extracting the coefficient of $y_1^{e_{i_0}}$ without logarithm in the Whittaker expansion along the first simple root, in the situation where that exponent has real part $1/2$ and the error exponent $\tau$ is larger. It is used by [`LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg`](thm.html#LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg) and [`LanglandsTunnell.CubicInduction.smoothingModule_slabForm`](thm.html#LanglandsTunnell.CubicInduction.smoothingModule_slabForm), where the stability, linearity and differentiation properties of the leading-coefficient map are what allows the borderline exponent to be excluded.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_smoothingModule_expansion_leadingCoeff.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.smoothingModule_expansion_leadingCoeff
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
          φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
            (fun g => ∑ i, c i * f (g * h * t i)) w})
    (m J : ℕ) (e : Fin m → ℂ) (he : Function.Injective e)
    (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ) (hτ : 1 / 2 < τ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ)
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2) :
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}) ∧
            ∀ (y₂ : ℝ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (fun g => w (g * k)) y₂ k' = (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k' * k)) ∧
    (∀ (z : ℂ), ∀ w₁ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ w₂ ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (z • w₁ + w₂) y₂ k = z * (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w₁ y₂ k + (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w₂ y₂ k) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, b i₀ j y₂ k = (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ k) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
          ((fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv i j w) y₂ k) 0) ∧
    (∀ w ∈ Submodule.span ℂ ((fun φ => smoothingOperator φ u) '' {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | IsSmoothingKernel φ ∧
        ∃ S : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            (fun g => φ (k⁻¹ * g)) ∈ Submodule.span ℂ (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))}), ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) w y₂ (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))
          ((fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - (fun (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) =>
        if h : 0 < y₂ ∧ 0 < J ∧ ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
  ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) then
          (Classical.choose h.2.2) i₀ ⟨0, h.2.1⟩ y₂ k
        else 0) (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0) := by sorry
