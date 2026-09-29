-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
-- name    : LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ac634802-de21-56a6-a905-0406e07ac0c4
-- title:
--   Entire twisted Euler products exclude Eisenstein eigensystems
-- statement:
--   Let $K$ be a number field and let $\Pi$ be a Hecke eigensystem over $K$ with complex coefficients, i.e. a nonzero level ideal of $\mathcal{O}_K$ together with two families $a_v, b_v \in \mathbb{C}$ indexed by the finite places $v$ of $K$ (the height-one primes of $\mathcal{O}_K$). Write $\varpi_v$ for the idele of $K$ that is a uniformizer in the completion at $v$ and $1$ at every other component, and $Nv$ for the absolute norm of $v$; call a continuous homomorphism $\chi\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ an idele class character if it kills the image of $K^\times$, unitary if $\|\chi(x)\| = 1$ for all $x$, and unramified at $v$ if it is trivial on those local units at $v$ lying, together with their inverses, in the valuation ring. Assume, for every continuous unitary idele class character $\chi$, that there are a finite set $S$ of finite places, a real $\sigma_0$ and an entire function $\Lambda$ on $\mathbb{C}$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the family indexed by the finite places $v \notin S$ of the reciprocals of $P_{v,\chi}((Nv)^{-s})$, where $P_{v,\chi}(X) = 1 - \chi(\varpi_v)a_v X + \chi(\varpi_v)^2 b_v X^2$ when $\chi$ is unramified at $v$ and $P_{v,\chi}(X) = 1$ otherwise, is unconditionally multipliable with product $\Lambda(s)$. Let $N \neq 0$ be an ideal of $\mathcal{O}_K$ and let $\mu_1, \mu_2$ be continuous idele class characters of $K$. Then $\Pi$ does not agree away from a finite set with the Eisenstein eigensystem of level $N$ attached to $(\mu_1,\mu_2)$: there is no finite set $T$ of finite places with $a_v = \mu_1(\varpi_v) + \mu_2(\varpi_v)$ and $b_v = \mu_1(\varpi_v)\mu_2(\varpi_v)$ for all $v \notin T$. The ideal $N$ enters only as the level of the Eisenstein eigensystem, which the agreement relation does not compare.
--
--   This is the cuspidality half of the converse-theorem package: a table of Hecke parameters all of whose unitary twists have entire (partial) standard $L$-functions cannot be the table of an Eisenstein series, because the Eisenstein Euler product is a product of two Hecke $L$-functions and inherits the pole of the Dedekind zeta function at $s=1$. It feeds the statements that an arithmetically realisable genuine cusp form, and its twists, are non-Eisenstein, and through these the construction of weight-one genuine cusp forms used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm Polynomial
open NumberField.TateGlobal LanglandsTunnell.Converse
open scoped Classical in

theorem LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (hent : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
      IsUnitaryChar (𝓞 K) K χ →
      ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        Differentiable ℂ Λ ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((if IsUnramifiedCharAt χ v.1
              then C 1 - C (((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
                + C ((((χ (uniformizerIdele K v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
              else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (_h₁ : IsIdeleClassChar (𝓞 K) K μ₁) (_h₂ : IsIdeleClassChar (𝓞 K) K μ₂)
    (_hc₁ : Continuous μ₁) (_hc₂ : Continuous μ₂) :
    ¬ Pi.AgreesAwayFromFinite (eisensteinTableOf K N hN μ₁ μ₂) := by sorry
