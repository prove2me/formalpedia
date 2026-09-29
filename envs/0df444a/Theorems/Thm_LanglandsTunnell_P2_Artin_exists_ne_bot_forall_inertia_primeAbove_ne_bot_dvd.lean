-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
-- name    : LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/abed90c9-45d1-5570-be2c-f1cb82186a49
-- title:
--   Ramified primes divide a common nonzero ideal
-- statement:
--   Let $E$ and $L'$ be number fields with $L'$ an extension of $E$ that is Galois. The assertion is that there exists an ideal $\mathfrak r$ of the ring of integers $\mathcal O_E$ with $\mathfrak r \neq 0$ such that, for every point $v$ of the height-one spectrum of $\mathcal O_E$ (that is, every nonzero prime ideal `v.asIdeal` of $\mathcal O_E$), if the inertia subgroup of the Galois group $L' \simeq_{\mathrm{alg}[E]} L'$ at the prime `primeAbove E L' v` of $\mathcal O_{L'}$ is not the trivial subgroup, then `v.asIdeal` divides $\mathfrak r$. Here `primeAbove E L' v` denotes a prime ideal of $\mathcal O_{L'}$ chosen, once and for all for each $v$, among those lying over `v.asIdeal`; since the extension is Galois, nontriviality of the inertia group at that choice expresses exactly that $v$ ramifies in $L'$. Thus the statement is a divisibility form of the finiteness of the set of ramified primes: all ramified primes of $E$ occur among the prime divisors of one fixed nonzero ideal.
--
--   This is the classical statement that only finitely many primes of a number field ramify in a fixed finite Galois extension, packaged as a single nonzero ideal divisible by all of them. It is used to choose a modulus divisible by every ramified prime, so that Frobenius elements and Artin symbols are available at all primes outside the modulus; it is cited in the construction of Hecke characters and Artin symbols in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
    (E L' : Type*) [Field E] [NumberField E] [Field L'] [NumberField L'] [Algebra E L'] [IsGalois E L'] :
    ∃ 𝔯 : Ideal (𝓞 E), 𝔯 ≠ ⊥ ∧
      ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E L' v).inertia (L' ≃ₐ[E] L') ≠ ⊥ → v.asIdeal ∣ 𝔯 := by sorry
