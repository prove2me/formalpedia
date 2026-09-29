-- Prove2me | Theorems.Thm_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
-- name    : HeckeCharacter.exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/bf9d12f1-c8d4-54bc-b62a-f05a87906d2a
-- title:
--   Uniform modulus for idele characters with prescribed ramification
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of height-one primes of $\mathcal{O}_K$ (finite places of $K$), and let $\rho$ assign to every finite place $v$ a group homomorphism $\rho_v\colon (K_v)^\times \to \mathbb{C}^\times$ from the units of the $v$-adic completion to $\mathbb{C}^\times$. Then there is a nonzero ideal $\mathfrak{f}$ of $\mathcal{O}_K$, depending only on $K$, $S$ and $\rho$, such that every group homomorphism $\chi\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ satisfying the following four conditions admits $\mathfrak{f}$ as a modulus in the sense of [`HeckeCharacter.AdmitsModulus`](def/HeckeCharacter_FiniteOrder.html#L21): $\chi$ is continuous as a map to $\mathbb{C}$; $\chi$ is unitary, i.e. $\lVert \chi(x)\rVert = 1$ for all ideles $x$; for every $v \notin S$ the local character `localChar` $\chi$ $v$ — that is, $\chi$ precomposed with the map sending $t \in (K_v)^\times$ to the idele with trivial archimedean part and finite part equal to $t$ at $v$ and $1$ elsewhere — is trivial on every $t$ with both $t$ and $t^{-1}$ in the valuation ring of $K_v$; and for every $v \in S$ this local character agrees with $\rho_v$ on all such $t$. Admitting the modulus $\mathfrak{f}$ means: $\chi(u) = 1$ for every idele unit $u$ whose archimedean component is $1$ and whose finite component satisfies, at every finite place $v$, $\lvert u_v \rvert_v = 1$ and $\lvert u_v - 1\rvert_v \le \exp(-n_v)$, where $n_v$ is the multiplicity of $v$ in the factorisation of $\mathfrak{f}$.
--
--   This is the statement that a family of continuous unitary idele characters with ramification constrained by the data $(S,\rho)$ has uniformly bounded conductor: a single nonzero modulus $\mathfrak{f}$ works for the whole family, so that each member factors through a fixed ray class group. It is used in the treatment of Tate's global zeta function, in the construction of the zero-free region and Euler-product continuation for characters with prescribed archimedean local behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal

theorem HeckeCharacter.exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
        IsUnitaryChar (𝓞 K) K χ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) →
        (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar χ v u = ρ v u) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 := by sorry
