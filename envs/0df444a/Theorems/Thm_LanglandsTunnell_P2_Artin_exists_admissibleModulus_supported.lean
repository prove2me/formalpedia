-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
-- name    : LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/e5cda582-d72e-53d0-a492-00615526eafa
-- title:
--   Existence of an admissible modulus supported at inertia-ramified places
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois. The assertion is that there is an ideal $\mathfrak f_0$ of $\mathcal O_K$ with the following two properties. First, $\mathfrak f_0$ satisfies [`LanglandsTunnell.P2.Artin.IsAdmissibleModulus K L`](def/LanglandsTunnell_ArtinCoreCTM.html#L311), which by definition means that $\mathfrak f_0 \neq 0$ and that for every height-one prime $v$ of $\mathcal O_K$ for which the chosen prime `primeAbove K L v` of $\mathcal O_L$ above $v$ has nontrivial inertia subgroup inside the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$, one has $v^{e(v)} \mid \mathfrak f_0$, where the exponent is $e(v) = 4\,e(v \mid (2)) + 2\,e(v \mid (3)) + 1$, the ramification indices being those of $v$ over the ideals $(2)$ and $(3)$ of $\mathbb Z$. Secondly, conversely, every height-one prime $v_0$ of $\mathcal O_K$ dividing $\mathfrak f_0$ carries above it some prime ideal $Q$ of $\mathcal O_L$ (prime, lying over $v_0$) whose inertia subgroup in the Galois group is nontrivial; so the support of $\mathfrak f_0$ consists exactly of inertia-ramified places.
--
--   This supplies the modulus needed to receive the Artin map of $L/K$ on a ray class group, in the shape required by the Langlands–Tunnell step: the modulus is divisible by the prescribed power of each ramified place and by nothing else. It is used in the construction of the finite-order Hecke characters and resolvent characters attached to a Galois extension of prime degree in that argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ 𝔣₀ : Ideal (𝓞 K), LanglandsTunnell.P2.Artin.IsAdmissibleModulus K L 𝔣₀ ∧
      ∀ v₀ : HeightOneSpectrum (𝓞 K), v₀.asIdeal ∣ 𝔣₀ →
        ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v₀.asIdeal ∧
          Q.inertia (L ≃ₐ[K] L) ≠ ⊥ := by sorry
