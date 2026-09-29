-- Prove2me | Theorems.Thm_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
-- name    : NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/0e083909-dca8-52df-a084-006e5f1c7ed1
-- title:
--   Norm group of the Kummer extension by p-th roots of S'-units
-- statement:
--   Let $E$ be a number field, $p$ a prime, and suppose the set of primitive $p$-th roots of unity in $E$ is nonempty. Let $S'$ be a finite set of height-one primes of $\mathcal O_E$ containing every $v$ with $p \in v$, and assume that the subgroup of principal idèles — the image of $E^\times$ in $(\mathbb A_E)^\times$ under the structure map — together with the subgroup of idèles whose finite component at each $v \notin S'$ lies, along with the component of the inverse, in the valuation ring of $E_v$, generate the whole idèle group: $\mathrm{principalIdeles} \sqcup \mathrm{unitIdelesOutside}\,S' = \top$. Then there is a number field $F'$, an $E$-algebra and Galois over $E$, whose Galois group $\mathrm{Gal}(F'/E)$ is commutative and satisfies $\sigma^p = 1$ for all $\sigma$, such that for every $v \notin S'$ and every prime $w$ of $\mathcal O_{F'}$ lying under to $v$ (i.e. $w \cap \mathcal O_E = v$) the inertia subgroup of $w$ in $\mathrm{Gal}(F'/E)$ is trivial, and such that $$\mathrm{principalIdeles} \sqcup \operatorname{range}\big(N_{F'/E}\big) = \mathrm{principalIdeles} \sqcup \operatorname{range}\big(x \mapsto x^p\big) \sqcup \mathrm{unitIdelesTrivialOn}\,S'.$$ Here $N_{F'/E}$ is the idelic norm attached to the base change `genuineBaseChange E F'`, namely the map on units induced by the algebra norm of $\mathbb A_{F'}$ over $\mathbb A_E$ for the canonical ring homomorphism $\mathbb A_E \to \mathbb A_{F'}$ together with its identification $\mathbb A_E \otimes_E F' \cong \mathbb A_{F'}$; and $\mathrm{unitIdelesTrivialOn}\,S'$ consists of those idèles that are local units outside $S'$, have trivial infinite part, and have finite component $1$ at every $w \in S'$.
--
--   This is the norm-group computation for the Kummer extension obtained by adjoining $p$-th roots of all $S'$-units, the step at the heart of the algebraic proof of the second inequality and of the existence theorem of class field theory. It is used in [`M4aHerbrand.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot`](thm.html#M4aHerbrand.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot), where the root of unity hypothesis is supplied in the form of an explicit primitive $p$-th root.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent
open NumberField

theorem NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
    (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty)
    (S' : Finset (HeightOneSpectrum (𝓞 E)))
    (hSp : ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ v.asIdeal → v ∈ S')
    (hS : principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) = ⊤) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F'),
      (∀ σ τ : F' ≃ₐ[E] F', σ * τ = τ * σ) ∧ (∀ σ : F' ≃ₐ[E] F', σ ^ p = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 E), v ∉ S' → ∀ w : HeightOneSpectrum (𝓞 F'),
        w.asIdeal.under (𝓞 E) = v.asIdeal → w.asIdeal.inertia (F' ≃ₐ[E] F') = ⊥) ∧
      principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F').idelicNorm).range
        = principalIdeles (𝓞 E) E
            ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
            ⊔ unitIdelesTrivialOn (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) := by sorry
