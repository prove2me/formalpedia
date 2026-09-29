-- Prove2me | Theorems.Thm_IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap
-- name    : IsLocalRing.exists_residueMap_of_surjective_residue_comp_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/85bd31df-3e3f-5ddc-b16d-b56b918c6429
-- title:
--   Residue map to k on a local Λ-algebra reaching its residue field
-- statement:
--   Let $\Lambda$ be a commutative local ring, $k$ a field, and $\mathrm{res}_0 : \Lambda \to k$ a ring homomorphism that is surjective and whose kernel is the maximal ideal of $\Lambda$. Let $T$ be a commutative local ring equipped with a $\Lambda$-algebra structure, and suppose that the composite of the structure map $\Lambda \to T$ with the canonical surjection $T \to T/\mathfrak m_T$ onto the residue field is surjective. The conclusion asserts the existence of a ring homomorphism $\mathrm{res}_T : T \to k$ such that $\mathrm{res}_T$ is surjective, the kernel of $\mathrm{res}_T$ is the maximal ideal of $T$, and for every $w \in \Lambda$ one has $\mathrm{res}_T(\mathrm{algebraMap}_{\Lambda,T}(w)) = \mathrm{res}_0(w)$, i.e. $\mathrm{res}_T$ restricts along the structure map to the given residue map $\mathrm{res}_0$ of $\Lambda$. No finiteness, Noetherian or Artinian hypotheses are imposed on $\Lambda$ or $T$.
--
--   This is the standard identification of the residue field of a local $\Lambda$-algebra $T$ whose residue field is reached from $\Lambda$, packaged so that such a $T$ may be replaced by a $T$ equipped with an explicit residue map to $k$ lying over $\mathrm{res}_0$. It is used in the functor-of-points description of deformation rings, where the test algebras are presented in the first form while the inputs require the second.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_residueMap_of_surjective_residue_comp_algebraMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_residueMap_of_surjective_residue_comp_algebraMap
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (k : Type) [Field k]
    (res₀ : Λ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal Λ)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra Λ T]
    (hT : Function.Surjective (⇑(residue T) ∘ ⇑(algebraMap Λ T))) :
    ∃ resT : T →+* k, Function.Surjective resT ∧ RingHom.ker resT = maximalIdeal T ∧
      ∀ w : Λ, resT (algebraMap Λ T w) = res₀ w := by sorry
