-- Prove2me | Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
-- name    : HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f1d9bfe4-9f36-50bc-9059-aa1ccc4c1377
-- title:
--   Finite-order Hecke character with prescribed values and signs
-- statement:
--   Let $K$ be a number field, $\mathfrak f$ a non-zero ideal of $\mathcal O_K$, $\psi$ a function from the height-one primes of $\mathcal O_K$ to $\mathbb C^\times$, and $\varepsilon$ a function from the real embeddings $\tau : K \to \mathbb R$ to $\mathbb C^\times$. Assume the ray law with signs: for every $\alpha \in \mathcal O_K$ with $\alpha \neq 0$ and $\alpha - 1 \in \mathfrak f$, the symbol $\prod_v \psi(v)^{\operatorname{ord}_v(\alpha \mathcal O_K)}$ (a finitely supported product over the height-one primes, with exponents the valuations of the fractional ideal attached to $\mathrm{span}\{\alpha\}$) equals $\prod \varepsilon(\tau)$ over those real embeddings $\tau$ with $\tau(\alpha) < 0$. The conclusion is the existence of a monoid homomorphism $\xi$ from the idele units $(\mathbb A_K)^\times$ to $\mathbb C^\times$ such that: (i) $\xi$ is trivial on the image of $K^\times$, continuous and of finite order; (ii) $\xi$ admits $\mathfrak f$ as modulus, i.e. $\xi(u) = 1$ whenever the archimedean component of $u$ is $1$ and its finite components satisfy $|u_v| = 1$ and $|u_v - 1| \le \exp(-n_v)$ at every $v$, where $n_v$ is the multiplicity of $v$ in $\mathfrak f$; (iii) $\|\xi(x)\| = 1$ for all $x$; (iv) for every height-one prime $v$ with $v \nmid \mathfrak f$, the value of $\xi$ on the idele which is a uniformiser at $v$ and $1$ at all other places and at the archimedean places is $\psi(v)$; and (v) for every real embedding $\tau$, the local component of $\xi$ at the infinite place determined by $\tau$ (that is, $\xi$ composed with the embedding of the units of that completion as ideles trivial elsewhere) sends $-1$ to $\varepsilon(\tau)$.
--
--   This is the existence half of the classical correspondence between characters of ray class groups with archimedean sign data and finite-order Hecke characters (Größencharaktere), together with the identification of the local components: unramified with value $\psi(v)$ at the uniformiser for $v \nmid \mathfrak f$, and a sign character with $\xi_\tau(-1) = \varepsilon(\tau)$ at each real place. It feeds the Langlands–Tunnell part of the argument, where it supplies the twisting character and the associated cusp form attached to a two-dimensional representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod.lean

import Mathlib
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Deep.NTSupply
open scoped nonZeroDivisors

theorem HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (ψ : HeightOneSpectrum (𝓞 K) → ℂˣ) (ε : (K →+* ℝ) → ℂˣ)
    (hψ : ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol K ψ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), ε τ) :
    ∃ ξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsFiniteOrderHeckeChar K ξ ∧ AdmitsModulus K ξ 𝔣 ∧ IsUnitaryChar (𝓞 K) K ξ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ξ (uniformizerIdele K v) = ψ v) ∧
      (∀ τ : K →+* ℝ,
        archLocalChar ξ (InfinitePlace.mk (Complex.ofRealHom.comp τ)) (-1) = ε τ) := by sorry
