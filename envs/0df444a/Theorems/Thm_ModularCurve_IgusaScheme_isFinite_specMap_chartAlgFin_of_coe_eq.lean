-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq
-- name    : ModularCurve.IgusaScheme.isFinite_specMap_chartAlgFin_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/36937d34-043f-5c4a-bd5a-fcfabff37a60
-- title:
--   Finiteness of the j-chart degeneracy map for Igusa schemes
-- statement:
--   Fix natural numbers $M,q,\ell$ with $M$ nonzero and $q,\ell$ prime, and a nonzero natural number $M'$ with $M' = M\ell$. For a nonzero level $N$, write $F_N$ for `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the Laurent series $\mathrm{qExpand}_{\mathbb{Q},d}(j)$ for the nonzero divisors $d \mid N$, where $\mathrm{qExpand}_{\mathbb{Q},d}$ is the ring endomorphism of $\mathbb{Q}(\!(q)\!)$ multiplying all exponents by $d$; and write `chartAlgFin N q` for the subalgebra of $F_N$, over the subring $\mathbb{Z}_{(q)}$ of rationals whose denominator is coprime to $q$, consisting of the elements integral over $\mathbb{Z}_{(q)}[\,j_N\,]$, with $j_N \in F_N$ the class of $j$. Let $\iota \colon$ `chartAlgFin M q` $\to$ `chartAlgFin M' q` be a $\mathbb{Z}_{(q)}$-algebra homomorphism, and let $e$ be a ring endomorphism of $\mathbb{Q}(\!(q)\!)$ which is either the identity or $\mathrm{qExpand}_{\mathbb{Q},\ell}$, such that for every $b$ the Laurent series underlying $\iota(b)$ equals $e$ applied to the Laurent series underlying $b$. Then the morphism of affine schemes $\mathrm{Spec}$(`chartAlgFin M' q`) $\to$ $\mathrm{Spec}$(`chartAlgFin M q`) induced by $\iota$ is finite.
--
--   This is the finiteness half of the modular equation for the degeneracy map from level $M\ell$ to level $M$, read on the affine chart of the Igusa scheme on which $j$ is finite. It supplies the finiteness input for the comparison of ranks along such a degeneracy map in [`ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict`](thm.html#ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isFinite_specMap_chartAlgFin_of_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isFinite_specMap_chartAlgFin_of_coe_eq
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ)
    (ι : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q))
    (e : LaurentSeries ℚ →+* LaurentSeries ℚ) (he : e = RingHom.id _ ∨ e = qExpand ℚ ℓ)
    (hι : ∀ b, (((ι b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        e ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) :
    IsFinite (Spec.map (CommRingCat.ofHom ι.toRingHom)) := by sorry
