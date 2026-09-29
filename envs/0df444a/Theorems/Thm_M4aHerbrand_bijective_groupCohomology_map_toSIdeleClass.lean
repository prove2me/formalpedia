-- Prove2me | Theorems.Thm_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass
-- name    : M4aHerbrand.bijective_groupCohomology_map_toSIdeleClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/326affd8-e807-5501-bc1b-bff86a27728c
-- title:
--   Positive-degree cohomology of idèle and S-idèle class groups agree
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $D$ be a Galois descent datum for the adèle ring of $F$ over $\mathcal{O}_F$ — that is, a homomorphism from $\mathrm{Gal}(F/E)$ to the ring automorphisms of $\mathbb{A}_F$ that is continuous in each $g$ and compatible with the structure map $F \to \mathbb{A}_F$ — and let $T$ be a set of height-one primes of $\mathcal{O}_F$. Assume that every $w \notin T$ has ramification index $1$ over the prime of $\mathcal{O}_E$ it lies over, and that $D$ stabilises the subgroup $U_F^T$ of `unitIdelesTrivialOn` (unit idèles outside $T$ which are trivial at the places in $T$), in the sense that the induced action on $(\mathbb{A}_F)^\times$ carries $U_F^T$ into itself. Assume given multiplicative actions of $\mathrm{Gal}(F/E)$ on $C_F = (\mathbb{A}_F)^\times/F^\times$ and on $C_{F,T} = (\mathbb{A}_F)^\times/(F^\times \cdot U_F^T)$ such that the first is the action $D.\mathrm{classAct}$ induced by $D$, and the second is compatible with $D.\mathrm{classAct}$ along the projection `toSIdeleClass`. Then for every subgroup $S \le \mathrm{Gal}(F/E)$ and every $n : \mathbb{N}$, the map induced on degree-$(n+1)$ group cohomology over $\mathbb{Z}$ by the projection $C_F \to C_{F,T}$, viewed as a morphism of $S$-representations by restriction, is bijective.
--
--   This is the comparison, for a Galois extension unramified outside $T$, between the cohomology of the idèle class group and that of the $T$-idèle class group in all positive degrees; it rests on the exactness of $1 \to U_F^T \to C_F \to C_{F,T} \to 1$ and the cohomological triviality of $U_F^T$. It is what transports the class-formation data (vanishing $H^1$ and cyclic $H^2$ with a fundamental class) from $C_F$ to $C_{F,T}$, and is cited in the construction of a fundamental class for the $S$-idèle class group and in the global duality statements for ramification restricted to $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

theorem M4aHerbrand.bijective_groupCohomology_map_toSIdeleClass
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1)
    (hT : D.StabilizesUnitIdeles T)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup (𝓞 F) F T)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F),
      g • toSIdeleClass (𝓞 F) F T c = toSIdeleClass (𝓞 F) F T (D.classAct g c))
    (S : Subgroup (F ≃ₐ[E] F)) (n : ℕ) :
    Function.Bijective ((groupCohomology.functor ℤ S (n + 1)).map ((Rep.resFunctor S.subtype).map
      (toSIdeleClassRepHom T (toSIdeleClass_smul_of_descent D T hact hactS)))).hom := by sorry
