-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- name    : LanglandsTunnell.exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/72421d94-fced-55f7-a124-b4a70d73529a
-- title:
--   Entire twisted L-functions of an induced Hecke eigensystem
-- statement:
--   Let $E \subseteq M$ be number fields with $[M:E]=2$, and let $\xi$ be a character of the idele units of $M$ with values in $\mathbb{C}^\times$ which is a finite-order Hecke character, i.e. trivial on the image of $M^\times$, continuous, and of finite order. Let $S_0$ be a finite set of primes of $\mathcal{O}_M$ such that for every $w' \notin S_0$ the character $\xi$ is unramified at $w'$, meaning that its local component at $w'$ kills every unit $t$ of the completion with both $t$ and $t^{-1}$ integral. Assume further that there are distinct primes $w' \neq w''$ of $\mathcal{O}_M$, both outside $S_0$, lying under the same prime of $\mathcal{O}_E$, with $\xi(\varpi_{w'}) \neq \xi(\varpi_{w''})$, where $\varpi_w$ denotes the idele with a uniformizer at $w$ and $1$ elsewhere. Let $\Pi$ be a Hecke eigensystem for $E$ over $\mathbb{C}$, that is a nonzero level ideal of $\mathcal{O}_E$ together with functions $a, b$ on the primes of $\mathcal{O}_E$ with complex values, and let $S$ be a finite set of primes of $\mathcal{O}_E$ such that for every $w \notin S$: whenever $w' \neq w''$ are primes of $\mathcal{O}_M$ both lying under $w$, one has $a_w = \xi(\varpi_{w'}) + \xi(\varpi_{w''})$ and $b_w = \xi(\varpi_{w'})\xi(\varpi_{w''})$; and whenever $w'$ lies under $w$ with inertia degree $\mathrm{inertiaDeg}'(w, w') = 2$, one has $a_w = 0$ and $b_w = -\xi(\varpi_{w'})$. Finally let $\chi$ be a continuous character of the idele units of $E$ with values in $\mathbb{C}^\times$ which is trivial on the image of $E^\times$ and satisfies $|\chi(x)| = 1$ for all $x$. Then there exist a finite set $S'$ of primes of $\mathcal{O}_E$, a real number $\sigma_0$ and a function $\Lambda : \mathbb{C} \to \mathbb{C}$ differentiable on all of $\mathbb{C}$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the family indexed by the primes $v \notin S'$ of the inverses of $P_v(\mathrm{N}v^{-s})$ is unconditionally multipliable with product $\Lambda(s)$; here $\mathrm{N}v$ is the absolute norm of $v$, and $P_v(X) = 1 - \chi(\varpi_v) a_v X + \chi(\varpi_v)^2 b_v X^2$ if $\chi$ is unramified at $v$ in the above sense, and $P_v(X) = 1$ otherwise.
--
--   This is the Hecke–Artin statement that the standard $L$-function of the eigensystem induced from a non-Galois-invariant finite-order Hecke character of a quadratic extension, twisted by an arbitrary unitary idele class character, continues to an entire function given in a right half-plane by its Euler product. It supplies the hypothesis of the criterion excluding Eisenstein (principal series) tables, and is cited in the construction of a genuine cusp form of archimedean weight one attached to such a character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Polynomial
  LanglandsTunnell.Converse

open scoped Classical in

theorem LanglandsTunnell.exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 E) E χ) (hcχ : Continuous χ)
    (huχ : IsUnitaryChar (𝓞 E) E χ) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 E)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      Differentiable ℂ Λ ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S'} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele E v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
              + C ((((χ (uniformizerIdele E v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by sorry
