-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
-- name    : NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/5aba17ab-f6cd-5474-b456-2c6a2af5f6e1
-- title:
--   Fujisaki compactness: compact representatives for norm-one ideles
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$, with ring of integers $\mathcal{O}_F$), and let $\mathbb{A}_F$ denote its adele ring, with idele group $\mathbb{A}_F^\times$ the unit group of $\mathbb{A}_F$ in its usual topology. Write $\mathbb{A}_F^1$ for the subgroup [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) of $\mathbb{A}_F^\times$, defined as the kernel of the character $\mathrm{distribHaarChar}$ of $\mathbb{A}_F$, i.e. the set of ideles $x$ such that multiplication by $x$ preserves an additive Haar measure on $\mathbb{A}_F$. The assertion is that there exists a subset $K$ of $\mathbb{A}_F^\times$ such that: $K$ is compact; $K$ is contained in $\mathbb{A}_F^1$; and for every $x \in \mathbb{A}_F^1$ there exist $\eta \in F^\times$ and $\kappa \in \mathbb{A}_F^\times$ with $\kappa \in K$ and $x$ equal to the product of the image of $\eta$ under the map of unit groups induced by the structure morphism $F \to \mathbb{A}_F$ with $\kappa$. No uniqueness of the decomposition is claimed, and compactness of $K$ refers to the topology of $\mathbb{A}_F^\times$.
--
--   This is Fujisaki's compactness theorem in the form of a compact set of representatives: the image of $K$ in $\mathbb{A}_F^1/F^\times$ is all of the norm-one idele class group, so it is the representative-set counterpart of the compactness of that quotient. It is used throughout the global theory of zeta integrals and automorphic forms on $\mathrm{GL}_1$ and $\mathrm{GL}_2$ over $F$, for instance in reducing integrals over $\mathbb{A}_F^1$ to integrals over a compact set and in constructing countable families of idele class characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
    (F : Type) [Field F] [NumberField F] :
    ∃ K : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact K ∧ K ⊆ (NumberField.TateGlobal.normOneIdeles F : Set _) ∧
      ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, ∃ (η : Fˣ) (κ : (AdeleRing (𝓞 F) F)ˣ), κ ∈ K ∧
        x = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η * κ := by sorry
