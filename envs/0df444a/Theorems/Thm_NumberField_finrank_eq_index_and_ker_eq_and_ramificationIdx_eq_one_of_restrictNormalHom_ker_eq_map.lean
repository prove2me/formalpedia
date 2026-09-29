-- Prove2me | Theorems.Thm_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
-- name    : NumberField.finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/cbc56df7-97ba-5d87-9d43-d6e93ab0b6ca
-- title:
--   Degree, kernel and ramification for the field cut out by H₀
-- statement:
--   Let $E \subseteq F \subseteq F'$ be number fields forming a tower ($F$ an $E$-algebra, $F'$ an $E$- and an $F$-algebra, compatibly), with $F'/E$ and $F/E$ Galois and with $\mathrm{Gal}(F'/E)$ commutative. Let $r' : (\mathbb{A}_E)^\times \to \mathrm{Gal}(F'/E)$ be a surjective group homomorphism from the units of the adèle ring of $E$, let $H_0$ be a subgroup of $(\mathbb{A}_E)^\times$ with $\ker r' \le H_0$, and assume that the kernel of the restriction homomorphism $\mathrm{Gal}(F'/E) \to \mathrm{Gal}(F/E)$ equals the image $r'(H_0)$. Then three things hold: first, $[F:E] = [(\mathbb{A}_E)^\times : H_0]$, the degree being the $E$-rank of $F$ and the right-hand side the subgroup index; second, every surjective homomorphism $r_F : (\mathbb{A}_E)^\times \to \mathrm{Gal}(F/E)$ with $H_0 \le \ker r_F$ has $\ker r_F = H_0$; third, for every nonzero prime $v$ of $\mathcal{O}_E$ such that the inertia subgroup in $\mathrm{Gal}(F'/E)$ of each nonzero prime of $\mathcal{O}_{F'}$ contracting to $v$ is contained in $r'(H_0)$, every nonzero prime $w$ of $\mathcal{O}_F$ contracting to $v$ satisfies $e(w/v) = 1$.
--
--   This is the descent step of the existence theorem of global class field theory — identifying the field cut out by a subgroup $H_0$ containing a norm group, together with its degree and its unramified places — isolated from the reciprocity input, which enters only through the existence of the surjection $r'$ onto the Galois group of the larger abelian extension $F'/E$. It is applied with $r'$ the reciprocity map of an auxiliary Kummer extension and $H_0$ an explicit open subgroup of the idèles, in the construction of a Galois extension with prescribed norm group in the Herbrand-quotient part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem NumberField.finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F'] [IsGalois E F]
    [IsMulCommutative (F' ≃ₐ[E] F')]
    (r' : (AdeleRing (𝓞 E) E)ˣ →* (F' ≃ₐ[E] F')) (hsurj : Function.Surjective r')
    (H₀ : Subgroup (AdeleRing (𝓞 E) E)ˣ) (hH₀ : r'.ker ≤ H₀)
    (hΓ : (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker = H₀.map r') :
    Module.finrank E F = H₀.index ∧
    (∀ rF : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F), Function.Surjective rF → H₀ ≤ rF.ker → rF.ker = H₀) ∧
    (∀ v : HeightOneSpectrum (𝓞 E),
      (∀ w' : HeightOneSpectrum (𝓞 F'), w'.asIdeal.under (𝓞 E) = v.asIdeal →
        w'.asIdeal.inertia (F' ≃ₐ[E] F') ≤ H₀.map r') →
      ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal.under (𝓞 E) = v.asIdeal →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) := by sorry
