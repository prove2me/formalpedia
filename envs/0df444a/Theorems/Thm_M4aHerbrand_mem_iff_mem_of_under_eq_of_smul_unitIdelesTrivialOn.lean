-- Prove2me | Theorems.Thm_M4aHerbrand_mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn
-- name    : M4aHerbrand.mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/4d756ac9-cbf6-5078-a9c0-cc748a1ffc3a
-- title:
--   A Galois-stable unit idèle group forces T to be fibred over E
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $D$ be an `IdeleGaloisDescent` for $\mathcal{O}_F$, $E$, $F$ — that is, a monoid homomorphism from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ which is compatible with the structure map $F \to \mathbb{A}_F$ (sending $\mathrm{algebraMap}\,x$ to $\mathrm{algebraMap}\,(g x)$) and is continuous in each $g$ — and let $T$ be a set of height-one primes of $\mathcal{O}_F$. Assume the group $F \simeq_{\mathrm{alg}[E]} F$ acts by group automorphisms on the subgroup `unitIdelesTrivialOn (𝓞 F) F T` of $\mathbb{A}_F^\times$, namely on the intersection of the units whose finite part and whose inverse's finite part are integral at every place $v \notin T$ with the units whose infinite part is $1$ and whose $w$-component is $1$ for every $w \in T$; assume further (hypothesis `hactU`) that this action is the one induced by $D$, i.e. for every $g$ and every $x$ in that subgroup the underlying unit idèle of $g \cdot x$ equals $D.\mathrm{unitsAct}\,g\,x$, the automorphism of $\mathbb{A}_F^\times$ obtained from the ring automorphism $D.\mathrm{act}\,g$. Then for any two height-one primes $w, w'$ of $\mathcal{O}_F$ lying under the same prime of $\mathcal{O}_E$, one has $w \in T$ if and only if $w' \in T$.
--
--   The statement extracts the hidden hypothesis implicit in equipping the group of $T$-trivial unit idèles with a Galois action: such a $T$ must be Galois-stable, hence a union of fibres of the map $w \mapsto w \cap \mathcal{O}_E$. It is used in the computation showing that the group cohomology of `unitIdelesTrivialOn` vanishes when the relevant ramification indices are $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

theorem M4aHerbrand.mem_iff_mem_of_under_eq_of_smul_unitIdelesTrivialOn
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x)
    (w w' : HeightOneSpectrum (𝓞 F)) (h : w.under (𝓞 E) = w'.under (𝓞 E)) :
    w ∈ T ↔ w' ∈ T := by sorry
