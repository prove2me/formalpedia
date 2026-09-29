-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg
-- name    : LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/1a18ffc5-6fd3-5d2b-bdaa-a0eb2fdae61c
-- title:
--   Smoothing submodule carrying the leading Whittaker coefficient at exponent 1/2
-- statement:
--   The data are: a character $\omega$ of the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$ with values in $\mathbb{C}^{\times}$, assumed unitary ($\|\omega(z)\|=1$ for all $z$, hypothesis `hω`); a function $f$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with complex values; natural numbers $n$, $m$, $J$; scalars $c : \mathrm{Fin}\,n \to \mathbb{C}$ and elements $t : \mathrm{Fin}\,n \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$; a further function $u$; an injective family of exponents $e : \mathrm{Fin}\,m \to \mathbb{C}$; a family of coefficient functions $a_{ij}(y_2,k)$; a real number $\tau$; and an index $i_0$.
--
--   The hypotheses on $f$ (the automorphy group) are: `hc`, continuity; `haut`, left invariance $f(\gamma g)=f(g)$ for $\gamma \in \mathrm{GL}_3(\mathbb{Q})$ embedded adelically by `globalPointsGL`; `hcen`, the central character identity $f(z\cdot g)=\omega(z)f(g)$ for $z$ an idele acting through `centralScalarGL`; `hmg`, moderate growth, that is $\|f(g)\| \le C\,\mathrm{gauge}_3(g)^N$ for some $C$ and $N$ and all $g$, where $\mathrm{gauge}_3 = \max(1, \mathrm{archGauge}_3\cdot\mathrm{finGauge}_3)$; `hP21` and `hP12`, cuspidality along the two standard two-dimensional unipotent radicals, i.e. $\int\!\int f(\mathrm{radicalP21}(x,y)\,g)=0$ and $\int\!\int f(\mathrm{radicalP12}(x,y)\,g)=0$ for all $g$, the integrals being taken against the measure of the carrier pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, namely additive Haar measure on $\mathbb{A}_{\mathbb{Q}}$ conditioned on the adelic box; `hsa`, archimedean smoothness in the sense of `IsArchSmooth3`, that for every $g$ the map $\varepsilon \mapsto f(g\cdot\mathrm{archRealLift3}\,\varepsilon)$ is $C^{\infty}$ on the set of real $3\times 3$ matrices of non-zero determinant; and `hKf`, that the right translates of $f$ by elements $k$ trivial at every finite place and orthogonal at the archimedean place (i.e. $\mathrm{archComponent3}(k) \in \mathrm{orth3}$) all lie in the span of one fixed finite set of functions.
--
--   The hypotheses on the translated combination are: `ht`, that each $t_i$ has trivial archimedean component; and `hz`, that $x \mapsto \sum_i c_i f(x\,t_i)$ is `IsCentreFinite`, i.e. for each of the three operators $\mathrm{casimir}_1 = \sum_i \partial_{ii}$, $\mathrm{casimir}_2 = \sum_{i,j}\partial_{ij}\partial_{ji}$, $\mathrm{casimir}_3 = \sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ built from the right archimedean derivatives $\partial_{ij} = \mathrm{archDeriv}\,i\,j$ there is a monic polynomial annihilating it (coefficients $a : \mathrm{Fin}(N+1)\to\mathbb{C}$ with $a(\mathrm{last}) = 1$ and $\sum_l a_l\,\mathrm{casimir}^{[l]}\varphi = 0$). The hypothesis `hu` places $u$ in the $\mathbb{C}$-span of the functions obtained by applying a finite list of operators $\partial_{ij}$ to $g \mapsto \sum_i c_i f(g\,h\,t_i)$, for arbitrary lists and arbitrary $h \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$.
--
--   The hypotheses on the Whittaker expansion of $u$ are: `he`, injectivity of $e$; `hcont`, that each $a_{ij}$ is continuous in $(y_2,k)$ on $\{y_2>0\}$; `hτ`, that $\tau > 1/2$; and `hexp`, that for every compact $K \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and every $b \ge 1$ there is a constant $C$ with
--   $$\Big\| W(u)\big(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\big) - \sum_{i<m}\sum_{j<J} a_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j} \Big\| \le C\,y_1^{\tau}$$
--   for all $k \in K$, all $y_2 \in [b^{-1},b]$ and all $0 < y_1 \le 1$; here $W = \mathrm{whittaker3}$ is the triple integral $W(\Phi)(g) = \int\!\int\!\int \Phi(\mathrm{upperUnipotent3}(x,y,z)\,g)\,\psi(-(x+y))$ against the same conditioned Haar measure, with $\psi$ the standard additive character `psiQ` of $\mathbb{A}_{\mathbb{Q}}$. Finally `hD` requires $\operatorname{Re} e_{i_0} = 1/2$.
--
--   The conclusion asserts the existence of a $\mathbb{C}$-submodule $M$ of the space of functions $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ and of a map $A$ assigning to a function $w$, a real number $y_2$ and a group element $k$ a complex number $A\,w\,y_2\,k$, such that all of the following hold.
--
--   First, every $w \in M$ is archimedean smooth, its Whittaker transform $W(w)$ is archimedean smooth, every iterated archimedean derivative $\partial_{i_1j_1}\cdots\partial_{i_rj_r}w$ along a finite list of index pairs is continuous, and $w$ is left invariant under $\mathrm{GL}_3(\mathbb{Q})$.
--
--   Second, there are $N_1,N_2,N_3$ and coefficient families $a^{(1)},a^{(2)},a^{(3)}$ on $\mathrm{Fin}(N_r+1)$, each with last coefficient $1$, such that for every $w \in M$ the corresponding monic polynomial in $\mathrm{casimir}_r$ annihilates $W(w)$, for $r = 1,2,3$.
--
--   Third, for every $w \in M$ there is a finite set $s$ of functions such that for every $k$ trivial at all finite places with $\mathrm{archComponent3}(k) \in \mathrm{orth3}$ the translate $g \mapsto w(gk)$ lies in the span of $s$.
--
--   Fourth, for every $w \in M$ and every such $k$, the translate $g \mapsto w(gk)$ again lies in $M$, and $A$ transforms accordingly: $A(w(\cdot\,k))\,y_2\,k' = A\,w\,y_2\,(k'k)$ for all $y_2$ and $k'$.
--
--   Fifth, $M$ is stable under each $\partial_{ij}$, $i,j \in \mathrm{Fin}\,3$.
--
--   Sixth, $A$ is $\mathbb{C}$-linear in its function argument on $M$: $A(z\,w_1 + w_2)\,y_2\,k = z\,A\,w_1\,y_2\,k + A\,w_2\,y_2\,k$ for $z \in \mathbb{C}$ and $w_1,w_2 \in M$.
--
--   Seventh, every $w \in M$ admits an expansion of the same shape as $u$: there are coefficient functions $b_{ij}$, continuous in $(y_2,k)$ on $\{y_2 > 0\}$, such that $b_{i_0 j}(y_2,k) = A\,w\,y_2\,k$ whenever $j$ has underlying natural number $0$ and $y_2 > 0$, and such that the expansion estimate with exponents $e_i$, log-powers $j < J$ and error exponent $\tau$ holds for $W(w)$ uniformly on compacta in $k$ and on bands $b^{-1}\le y_2 \le b$.
--
--   Eighth, $A$ differentiates the right action: for $w \in M$, indices $i,j$, and all $y_2$ and $k$, the function $s \mapsto A\,w\,y_2\,(k\cdot\mathrm{archRealLift3}(1 + s\,E_{ij}))$ has derivative $A(\partial_{ij}w)\,y_2\,k$ at $s = 0$.
--
--   Ninth, for $c_1 < c_2$ in $\mathrm{Fin}\,3$, the function $s \mapsto A\,w\,y_2\,(k\cdot R_{c_1c_2}(s))$, where $R_{c_1c_2}(s)$ is the archimedean lift of the rotation by $s$ in the $(c_1,c_2)$-plane, has derivative $A(\partial_{c_2c_1}w)\,y_2\,k - A(\partial_{c_1c_2}w)\,y_2\,k$ at $s = 0$.
--
--   Tenth, there is a form $B$ on pairs of functions such that: $B\,w'\,w = \overline{B\,w\,w'}$ for $w,w' \in M$; $B$ is linear in its first argument, $B(z\,w_1+w_2)\,w' = z\,B\,w_1\,w' + B\,w_2\,w'$; $\operatorname{Re}(B\,w\,w) > 0$ for every non-zero $w \in M$; each $\partial_{ij}$ is skew with respect to $B$, $B(\partial_{ij}w)\,w' = -\,B\,w\,(\partial_{ij}w')$; and $B$ is invariant under simultaneous right translation by any $k$ trivial at all finite places with orthogonal archimedean component, $B(w(\cdot\,k))\,(w'(\cdot\,k)) = B\,w\,w'$.
--
--   Eleventh, a recovery statement for the original data: if $A\,w\,y_2\,k = 0$ for all $w \in M$, all $y_2 > 0$ and all $k$, then $a_{i_0 j}(y_2,k) = 0$ for every $j$ with underlying natural number $0$, every $y_2>0$ and every $k$.
--
--   Twelfth, there are $N_1,N_2,N_3$ and coefficient families with last coefficient $1$ such that the corresponding monic polynomials in $\mathrm{casimir}_1,\mathrm{casimir}_2,\mathrm{casimir}_3$ annihilate $w$ itself, for every $w \in M$.
--
--   Thirteenth, every $v \in M$ has central character $\omega$: $v(z\cdot g) = \omega(z)\,v(g)$ for every idele $z$ and every $g$.
--
--   Fourteenth, every $v \in M$ has uniform moderate growth in all archimedean derivatives: there is an exponent $N$ such that for every finite list of index pairs there is a constant $C$ with $\|(\partial_{i_1j_1}\cdots\partial_{i_rj_r}v)(g)\| \le C\,\mathrm{gauge}_3(g)^{N}$ for all $g$.
--
--   This is the construction step of the archimedean argument that excludes a Whittaker exponent of real part $1/2$ for a cuspidal vector on $\mathrm{GL}_3$ over $\mathbb{Q}$: from one vector $u$ with a given expansion it produces a module $M$ of right smoothings, closed under the archimedean derivatives and under the relevant right translations, equipped with a linear functional $A$ extracting the coefficient of $y_1^{e_{i_0}}(\log y_1)^0$, with an invariant positive-definite form for which the derivatives are skew, with central finiteness and central character, and with the property that vanishing of $A$ on $M$ forces vanishing of the original coefficient. It is used by [`LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate`](thm.html#LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate), within the $\mathrm{GL}_3$ input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg.lean

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
LanglandsTunnell.CubicInduction.exists_smoothingSubmodule_leadingCoeff_form_of_expCoeff_re_eq_one_half_centreFinite_mg
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
    ∃ (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (A : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g) ∧
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l]
            (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w))) = 0) ∧
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M ∧
            ∀ (y₂ : ℝ) (k' : AdelicGL 3 (𝓞 ℚ) ℚ), A (fun g => w (g * k)) y₂ k' = A w y₂ (k' * k)) ∧
      (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M) ∧
      (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        A (z • w₁ + w₂) y₂ k = z * A w₁ y₂ k + A w₂ y₂ k) ∧
      (∀ w ∈ M, ∃ b : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => b i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, b i₀ j y₂ k = A w y₂ k) ∧
        ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ bd : ℝ, 1 ≤ bd → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, bd⁻¹ ≤ y₂ → y₂ ≤ bd → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ w
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, b i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) ∧
      (∀ w ∈ M, ∀ i j : Fin 3, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0))
          (A (WhittakerBlock.archDeriv i j w) y₂ k) 0) ∧
      (∀ w ∈ M, ∀ c₁ c₂ : Fin 3, c₁ < c₂ → ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => A w y₂ (k * WhittakerBlock.archRealLift3 (fun i j =>
            if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
            if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
            if i = j then 1 else 0)))
          (A (WhittakerBlock.archDeriv c₂ c₁ w) y₂ k - A (WhittakerBlock.archDeriv c₁ c₂ w) y₂ k) 0) ∧
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w') ∧
      ((∀ w ∈ M, ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, A w y₂ k = 0) →
        ∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, a i₀ j y₂ k = 0) ∧
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0) ∧
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g) ∧
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N) := by sorry
