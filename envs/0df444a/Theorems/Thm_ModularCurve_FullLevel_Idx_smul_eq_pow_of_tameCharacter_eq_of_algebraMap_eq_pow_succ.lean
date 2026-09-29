-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
-- name    : ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b6442df2-5265-58d2-9c0e-e7d86ed10c96
-- title:
--   Inertia of tame value α sends ζ to ζ^{N(α)}
-- statement:
--   Fix a natural number $q$ assumed prime, and let $P$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb Q}$ belongs to $P.\mathrm{nonunits}$. Let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{q^2-1} = q$, and let $\iota$ be a ring homomorphism from the field `GaloisField q 2` of $q^2$ elements into the residue field of $P$. Let $\tau$ be a $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lying in the inertia subgroup of $P$ over $\mathbb Q$, viewed inside the full automorphism group as the image of the inertia subgroup under the inclusion of the decomposition subgroup. Let $\alpha$ be a unit of `GaloisField q 2` whose image $\iota(\alpha)$ equals the tame value `P.tameCharacter π τ`, namely the residue of $\tau(\pi)/\pi$ when that quotient lies in $P$, and $0$ otherwise. Let $d$ be a unit of $\mathbb Z/q$ whose image under the structure map $\mathbb Z/q \to$ `GaloisField q 2` equals $\alpha^{q+1}$. Then for every $\zeta$ in `Idx q`, that is, every primitive $q$-th root of unity in $\overline{\mathbb Q}$, the element $\tau \bullet \zeta$ equals `ζ.pow d`, the primitive $q$-th root of unity $\zeta^{(d : \mathbb Z/q).val}$.
--
--   The labels `Idx q` index the geometric connected components of the modular curve of full level $q$, distinguished by the value of the Weil pairing on the chosen basis of the $q$-torsion; the statement computes the permutation of these labels induced by an inertia element at a place above $q$, showing that it is raising to the norm $N(\alpha) = \alpha^{q+1}$ of the tame value $\alpha$. It is used in the inertia clauses describing the Galois action on the charts of the semistable covering near the Igusa points, in particular in [`ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause`](thm.html#ModularCurve.FullLevel.exists_forall_mem_dom_teleChart_eIg_arithmeticGalois_smul_of_inertiaIgusaInftyClause) and its variants for $q = 2$ and $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelJacobian
import Mathlib.FieldTheory.Finite.GaloisField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (α : (GaloisField q 2)ˣ) (hα : ι (α : GaloisField q 2) = P.tameCharacter π τ)
    (d : (ZMod q)ˣ) (hd : algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1))
    (ζ : Idx q) :
    τ • ζ = ζ.pow d := by sorry
