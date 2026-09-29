-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
-- name    : LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/042c2af5-c4d7-56d3-8544-6426a9df7d3e
-- title:
--   Uniform ray exponent >1/2 for GL₃ Whittaker derivative words
-- statement:
--   Let $\omega$ be a homomorphism from the idele group of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $|\omega(z)|=1$ for all $z$, and let $a_2 : \mathrm{Fin}(N_2+1)\to\mathbb{C}$ and $a_3 : \mathrm{Fin}(N_3+1)\to\mathbb{C}$ be coefficient families that are monic in the sense $a_2(N_2)=a_3(N_3)=1$. The assertion is that there exists a real $\theta_0>1/2$, depending only on these data, with the following property. Let $f : GL_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous, invariant under left translation by the image of $GL_3(\mathbb{Q})$, satisfying $f(zg)=\omega(z)f(g)$ for central adelic scalars $z$, of moderate growth in the sense that $\|f\|$ is bounded by a constant times a power of $\max(1,\mathrm{archGauge}_3\cdot\mathrm{finGauge}_3)$, and cuspidal along both $P_{21}$ and $P_{12}$, meaning that the double integrals of $f(\mathrm{radicalP21}\,[x,y]\cdot g)$ and of $f(\mathrm{radicalP12}\,[x,y]\cdot g)$ vanish for all $g$, the integrals being taken against the Haar measure on $\mathbb{A}_\mathbb{Q}$ conditioned on the adelic box (the pins used throughout are `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`). Assume further: for some finite set $S$ of finite places, $f$ is right invariant under the image of `localMaximalCompact3` at every $p\notin S$; at every finite place $v$ there is an open subgroup $U_v\le GL_3(\mathbb{Q}_v)$ whose image fixes $f$ under right translation; $f$ is archimedean-smooth, i.e. $e\mapsto f(g\cdot\mathrm{archRealLift3}\,e)$ is $C^\infty$ on the locus of invertible real $3\times 3$ matrices for every $g$; and there is a finite set $s$ of functions such that $g\mapsto f(gk)$ lies in the $\mathbb{C}$-span of $s$ for every $k$ with trivial components at all finite places and orthogonal archimedean component. Let $n\in\mathbb{N}$, $c : \mathrm{Fin}\,n\to\mathbb{C}$ and $t : \mathrm{Fin}\,n\to GL_3(\mathbb{A}_\mathbb{Q})$ with each $t_i$ having trivial archimedean component, and put $v(x)=\sum_i c_i f(x t_i)$. Assume $v$ is centre-finite, i.e. annihilated by some monic polynomial in each of the operators `casimir1`, `casimir2`, `casimir3` built from the archimedean right derivatives `archDeriv`, and assume in addition the two specific relations $\sum_m a_2(m)\,\mathrm{casimir2}^{[m]}v=0$ and $\sum_m a_3(m)\,\mathrm{casimir3}^{[m]}v=0$. Then for every word $w$ in $\mathrm{Fin}\,3\times\mathrm{Fin}\,3$, every $h\in GL_3(\mathbb{A}_\mathbb{Q})$ and every $y_2>0$ there is a constant $C$ such that for all $0<y_1\le 1$ the Whittaker integral `whittaker3` against the standard additive character $\psi_\mathbb{Q}$ of the iterated derivative $\partial_w v$ (the right fold of $\mathrm{archDeriv}$ along $w$) evaluated at $\mathrm{archRealLift3}(\mathrm{diag}(y_1y_2,y_2,1))\cdot h$ has norm at most $C\,y_1^{\theta_0}$.
--
--   This is the one-direction (first simple root) decay estimate for Whittaker functions attached to derivative words of a centre-finite combination of right translates of a cuspidal function on $GL_3(\mathbb{A}_\mathbb{Q})$: the exponent $\theta_0>1/2$ is fixed in advance by the central character and the two Casimir polynomials, and is then uniform over all forms and all translates and words. It feeds the ray-order statement [`LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant`](thm.html#LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_rayOrder_whittaker3_of_isCentreFinite_of_isRightInvariant) in the cubic-induction block used for the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant.lean

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
LanglandsTunnell.CubicInduction.exists_one_half_lt_forall_foldr_archDeriv_rayOrder_whittaker3_of_casimir_relations_of_isRightInvariant
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1) :
    ∃ θ₀ : ℝ, 1 / 2 < θ₀ ∧
      ∀ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous f →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) →
      IsModerateGrowth3 ℚ f →
      IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f →
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f →
      ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g) →
      WhittakerBlock.IsArchSmooth3 f →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ), (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) →
      IsCentreFinite (fun x => ∑ i, c i * f (x * t i)) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] fun x => ∑ i, c i * f (x * t i)) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] fun x => ∑ i, c i * f (x * t i)) = 0) →
      ∀ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
      ∀ y₂ : ℝ, 0 < y₂ → ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ
            (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun x => ∑ i, c i * f (x * t i)) w)
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * h)‖ ≤
          C * y₁ ^ θ₀ := by sorry
