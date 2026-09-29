-- Prove2me | Theorems.Thm_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
-- name    : NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/02e2eb69-47e7-5407-8ace-d37c88493eb0
-- title:
--   Twisting a unitary idele class character by ‖·‖^{it₀}
-- statement:
--   Let $K$ be a number field, let $\chi$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function is continuous, which is unitary ($\lVert\chi(x)\rVert=1$ for every idele unit $x$) and trivial on principal ideles ($\chi(\iota(u))=1$ for all $u\in K^\times$, $\iota$ the unit map of $K\to\mathbb{A}_K$), and let $t_0\in\mathbb{R}$. Here `normPowChar K t₀` is $x\mapsto \lVert x\rVert^{it_0}$ with $\lVert x\rVert$ the module of $x$ (the value of the distributive Haar character on the adeles). Then the twist $\chi\cdot\lVert\cdot\rVert^{it_0}$ is again unitary, trivial on principal ideles and continuous; for every finite place $v$ of $\mathcal{O}_K$ and every $u\in (K_v)^\times$ with $u$ and $u^{-1}$ in the valuation ring, the twist and $\chi$ agree on the idele which is $u$ at $v$ and $1$ elsewhere; consequently the twist is unramified at $v$ (its local component trivial on such $u$) exactly when $\chi$ is, and the truncated Euler coefficients satisfy: the value at the uniformizer idele of $v$, taken to be $0$ at ramified places, equals that of $\chi$ times $N(v)^{-it_0}$. Moreover, for $\tau:\{\text{infinite places}\}\to\mathbb{R}$, if the local component of $\chi$ at each infinite place $v$ equals $\lVert\cdot\rVert^{i\tau_v}$ on units with positive real and vanishing imaginary part under the completion embedding, the twist satisfies the same with $\tau_v+t_0$; and for $m:\{\text{infinite places}\}\to\mathbb{Z}$, if $\chi$'s local component is $x\mapsto x^{m_v}$ on units of modulus one, so is the twist's.
--
--   This is the standard behaviour of Hecke characters under twisting by a unitary power of the idelic norm, in the form needed for Tate-style analysis: the unit parts, ramification and archimedean weights are unchanged, the archimedean parameters shift by $t_0$ and the Euler coefficients acquire $N(v)^{-it_0}$. It is used in the construction of Euler products attached to adelic automorphic forms and in the Paley–Wiener style estimates for them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
    (t₀ : ℝ) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (χ * normPowChar K t₀) ∧
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (χ * normPowChar K t₀) ∧
    (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ * normPowChar K t₀) z : ℂˣ) : ℂ)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      localChar (χ * normPowChar K t₀) v u = localChar χ v u) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt (χ * normPowChar K t₀) v ↔ IsUnramifiedCharAt χ v) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      (if IsUnramifiedCharAt (χ * normPowChar K t₀) v
        then (((χ * normPowChar K t₀) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) =
      (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t₀))) ∧
    (∀ τ : InfinitePlace K → ℝ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (χ * normPowChar K t₀) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v + t₀ : ℝ) : ℂ) * Complex.I)) ∧
    (∀ m : InfinitePlace K → ℤ,
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) →
      ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar (χ * normPowChar K t₀) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) := by sorry
