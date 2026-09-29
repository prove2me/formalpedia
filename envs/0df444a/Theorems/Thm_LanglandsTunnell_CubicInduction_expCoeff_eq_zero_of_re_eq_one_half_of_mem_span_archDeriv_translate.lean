-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate
-- name    : LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/aab59651-98b3-59f2-a8d1-81965f578dbf
-- title:
--   Vanishing of the logarithm-free coefficient at exponent of real part 1/2
-- statement:
--   Let $\omega$ be a character of the idele units $(\mathbb{A}_{\mathbb{Q}})^\times$ with values in $\mathbb{C}^\times$ all of whose values have absolute value $1$, and let $f \colon \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_3(\mathbb{Q})$, transforming under central adelic scalars by $\omega$, of moderate growth in the sense that $f$ is slowly increasing on all of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ for the gauge `gauge3`, cuspidal along both standard maximal parabolics in the sense that the iterated integrals of $f$ over the two two-dimensional radical unipotents $\mathrm{radicalP21}$ and $\mathrm{radicalP12}$ vanish at every $g$ (the integrations being against the adelic additive Haar measure conditioned on the adelic box, for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`), archimedean-smooth in the sense that for every $g$ the map $e \mapsto f(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e \neq 0\}$, and such that for some finite set $s$ of functions, the right translate $g \mapsto f(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ whose components at all height-one primes are trivial and whose archimedean component satisfies $k^{\mathrm{T}}k = 1$. Fix $n$, scalars $c_i$ and elements $t_i$ with trivial archimedean component, and assume the combination $x \mapsto \sum_i c_i f(x t_i)$ is `IsCentreFinite`, i.e. annihilated by a monic polynomial in each of the three operators `casimir1`, `casimir2`, `casimir3`. Let $u$ lie in the $\mathbb{C}$-span of the functions obtained from $g \mapsto \sum_i c_i f(ght_i)$, for arbitrary $h$, by applying finite lists of the archimedean directional derivatives $\mathrm{archDeriv}\,i\,j$. Let $m, J \in \mathbb{N}$, let $e \colon \mathrm{Fin}\,m \to \mathbb{C}$ be injective, let $a_{ij}(y_2,k)$ be functions that are jointly continuous on $\{y_2 > 0\}$, let $\tau > 1/2$, and suppose that for every compact $K$ and every $b \ge 1$ there is $C$ with $$\Bigl\| W(u)\bigl(\mathrm{archRealLift3}\,\mathrm{diag}(y_1y_2,y_2,1)\cdot k\bigr) - \sum_{i,j} a_{ij}(y_2,k)\,y_1^{e_i}(\log y_1)^{j}\Bigr\| \le C\,y_1^{\tau}$$ for all $k \in K$, all $b^{-1} \le y_2 \le b$ and all $0 < y_1 \le 1$, where $W(u)$ is the Whittaker integral `whittaker3` of $u$ against the standard additive character `psiQ` for the same pins. Finally fix $i_0$ with $\operatorname{Re}(e_{i_0}) = 1/2$, assume $a_{ij}$ vanishes identically on $\{y_2>0\}$ whenever $\operatorname{Re}(e_i) < 1/2$, and assume $a_{i_0 j}$ vanishes identically for every $j \ge 1$. Then $a_{i_0 j}$ vanishes at every $y_2 > 0$ and every $k$ also for the index $j = 0$.
--
--   This is the final step in ruling out exponents on the critical line $\operatorname{Re}(s) = 1/2$ in the asymptotic expansion of a Whittaker coefficient of a cusp form on $\mathrm{GL}_3$ over $\mathbb{Q}$: once the logarithmic coefficients at such an exponent are known to vanish, so does the logarithm-free one. It feeds into the statement that all archimedean derivatives of the Whittaker coefficient decay with ray order exceeding $1/2$, used in the $\mathrm{GL}_3$ input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate.lean

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
LanglandsTunnell.CubicInduction.expCoeff_eq_zero_of_re_eq_one_half_of_mem_span_archDeriv_translate
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
    (i₀ : Fin m) (hD : (e i₀).re = 1 / 2)
    (hmin : ∀ (i : Fin m) (j : Fin J), (e i).re < 1 / 2 →
      ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, a i j y₂ k = 0)
    (hlog : ∀ j : Fin J, 1 ≤ (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, a i₀ j y₂ k = 0) :
    ∀ j : Fin J, (j : ℕ) = 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, a i₀ j y₂ k = 0 := by sorry
