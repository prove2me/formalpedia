-- Prove2me | Theorems.Thm_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
-- name    : IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/2ce1edbe-0ecc-5089-94eb-785e2013f10e
-- title:
--   Unique lifting of residue embeddings into complete local algebras
-- statement:
--   Let $V$ be a Noetherian commutative local ring and let $D$ be a commutative local ring equipped with a $V$-algebra structure whose structure map $V \to D$ is a local homomorphism and makes $D$ a flat $V$-module; assume that $(\mathfrak m_V)D = \mathfrak m_D$, i.e. the image ideal of the maximal ideal of $V$ under $V \to D$ is the maximal ideal of $D$, and that the residue field extension $\kappa(D)/\kappa(V)$ is finite and separable. Let $E$ be a commutative local ring which is complete and separated for the $\mathfrak m_E$-adic topology (`IsAdicComplete (maximalIdeal E) E`) and is a $V$-algebra; no Noetherian hypothesis is imposed on $E$, nor is the map $V \to E$ assumed local. Let $\iota : \kappa(D) \to \kappa(E)$ be a ring homomorphism compatible with the two maps from $V$, in the sense that $\iota(\overline{v_D}) = \overline{v_E}$ for every $v \in V$, where $v_D$ and $v_E$ denote the images of $v$ in $D$ and in $E$. Then there is exactly one $V$-algebra homomorphism $g : D \to E$ with $\overline{g(d)} = \iota(\bar d)$ in $\kappa(E)$ for all $d \in D$.
--
--   This is the universal property of an unramified flat local extension $V \to D$ with respect to complete local $V$-algebras: a prescribed residue-field embedding lifts uniquely. It is used to produce finite étale algebras over adic completions, via [`AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq`](thm.html#AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (E : Type) [CommRing E] [IsLocalRing E] [IsAdicComplete (maximalIdeal E) E] [Algebra V E]

    (ι : ResidueField D →+* ResidueField E)
    (hι : ∀ v : V, ι (residue D (algebraMap V D v)) = residue E (algebraMap V E v)) :
    ∃! g : D →ₐ[V] E, ∀ d : D, residue E (g d) = ι (residue D d) := by sorry
