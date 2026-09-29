-- Prove2me | Theorems.Thm_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
-- name    : MvPowerSeries.exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/68bb1a9f-217e-5d05-93cd-4d6c0f9961ae
-- title:
--   Freeness on a basic open chart for power series quotients
-- statement:
--   Let $B$ be a commutative Noetherian ring and let $I$ be an ideal of the two-variable power series ring $B[\![x_0,x_1]\!]$ (formally, `MvPowerSeries (Fin 2) B`). Assume that the quotient $B[\![x_0,x_1]\!]/I$ is a finite $B$-module and a projective $B$-module, and that some power of each variable lies in $I$: there is $q \in \mathbb{N}$ with $x_i^{q} \in I$ for both $i \in \{0,1\}$. Let $\mathfrak m$ be a maximal ideal of $B$. The assertion is that there exists $g \in B$ with $g \notin \mathfrak m$ such that for every commutative ring $R'$ equipped with a $B$-algebra structure for which the image of $g$ under $\mathrm{algebraMap}\;B\;R'$ is a unit of $R'$, the $R'$-module $$R'[\![x_0,x_1]\!] \big/ I\,R'[\![x_0,x_1]\!]$$ is free, where $I\,R'[\![x_0,x_1]\!]$ means the image ideal `I.map (MvPowerSeries.map (algebraMap B R'))`. The quantification over $R'$ is internal to the conclusion, so a single $g$ works simultaneously for all such base changes (for instance $B[1/g]$, $B[1/(gg')]$, or $B_{\mathfrak m}$).
--
--   This is a spreading-out, or "free chart", statement: a finite projective quotient of a two-variable power series ring with nilpotent coordinates becomes free after inverting a single element off a given maximal ideal, and stays free over every base in which that element is invertible. It is used in the construction of formal modules in the Čerednik–Drinfeld part of the development, where a free basis over a basic open of the base is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPowerSeries.exists_notMem_and_forall_free_quotient_map_of_projective_of_isMaximal
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal (MvPowerSeries (Fin 2) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ g : B, g ∉ 𝔪 ∧ ∀ (R' : Type) [CommRing R'] [Algebra B R'], IsUnit (algebraMap B R' g) →
      Module.Free R' (MvPowerSeries (Fin 2) R' ⧸ I.map (MvPowerSeries.map (algebraMap B R'))) := by sorry
