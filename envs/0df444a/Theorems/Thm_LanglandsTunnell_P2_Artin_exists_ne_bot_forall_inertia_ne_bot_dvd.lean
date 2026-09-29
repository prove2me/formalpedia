-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd
-- name    : LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ed882649-91a8-5c38-a40d-dbc03fd0996e
-- title:
--   Ramified primes divide a fixed nonzero ideal
-- statement:
--   Let $E$ and $L'$ be number fields with $L'$ a Galois extension of $E$. The assertion is the existence of an ideal $\mathfrak r$ of the ring of integers $\mathcal O_E$ with $\mathfrak r \neq 0$ such that the following holds: for every height-one prime $v$ of $\mathcal O_E$ (an element of the height-one spectrum, so given by a nonzero prime ideal `v.asIdeal`) and every ideal $Q$ of $\mathcal O_{L'}$ which is maximal and satisfies $Q \cap \mathcal O_E = v.asIdeal$ (the contraction of $Q$ along $\mathcal O_E \to \mathcal O_{L'}$ equals `v.asIdeal`), if the inertia subgroup of $Q$ in the Galois group $\mathrm{Gal}(L'/E) = L' \simeq_{\text{alg}[E]} L'$ is nontrivial, then `v.asIdeal` divides $\mathfrak r$. Thus a single nonzero ideal of $\mathcal O_E$ is divisible by every prime of $E$ admitting some maximal ideal above it with nontrivial inertia; ramification is tested at every maximal ideal of $\mathcal O_{L'}$ lying over $v$ rather than at a distinguished one.
--
--   This is the finiteness of the ramification locus of a finite Galois extension of number fields, packaged as a divisibility statement: the ramified primes all divide one fixed nonzero ideal. It is used to choose a modulus divisible by all ramified primes, so that Frobenius elements at the remaining primes are well defined; it is cited in the construction of resolvent sign characters and in the idelic norm and place-counting arguments of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd
    (E L' : Type*) [Field E] [NumberField E] [Field L'] [NumberField L'] [Algebra E L'] [IsGalois E L'] :
    ∃ 𝔯 : Ideal (𝓞 E), 𝔯 ≠ ⊥ ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (Q : Ideal (𝓞 L')), Q.IsMaximal → Q.under (𝓞 E) = v.asIdeal →
        Q.inertia (L' ≃ₐ[E] L') ≠ ⊥ → v.asIdeal ∣ 𝔯 := by sorry
