-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_mvPowerSeries_algEquiv_of_residue_surjective
-- name    : IsRegularLocalRing.exists_mvPowerSeries_algEquiv_of_residue_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-16T17:09:51.165685+00:00
-- url     : https://prove2.me/theorems/3581d615-dbd3-46c3-8f6f-39f60220109f
-- title:
--   Complete regular local algebras are formal power-series rings
-- statement:
--   Let $K$ be a field and let $A$ be a regular Noetherian local $K$-algebra, complete with respect to its maximal ideal $\mathfrak m$. Assume that the coefficient map induces a surjection $K\to A/\mathfrak m$. Then for some finite integer $r$ there is an isomorphism of $K$-algebras
--   $$K[[t_1,\ldots,t_r]]\cong A.$$
--   In particular, this isomorphism preserves the given coefficient field. The characteristic is unrestricted, and the field and algebra may belong to different universes. Because $K$ and $A/\mathfrak m$ are fields, the assumed surjection is an isomorphism. This is the regular equicharacteristic complete-local structure theorem with a supplied coefficient field; existence of a coefficient-field embedding is not assumed to follow from completeness alone.
-- source:
--   Stacks Project, Lemma 10.160.10(2), Tag 0C0S, https://stacks.math.columbia.edu/tag/0C0S . The coefficient map inducing the residue-field isomorphism is supplied explicitly. The proof uses a minimal generating family of the maximal ideal, completeness for surjectivity, and dimension drop for a nonzero kernel. The preliminary formal presentation is the coefficient-field case of Theorem 10.160.8, Tag 032A, https://stacks.math.columbia.edu/tag/032A .

import Mathlib
set_option autoImplicit false
open IsLocalRing
universe u v

theorem IsRegularLocalRing.exists_mvPowerSeries_algEquiv_of_residue_surjective
    (K : Type u) [Field K] (A : Type v) [CommRing A]
    [IsRegularLocalRing A] [Algebra K A] [IsAdicComplete (maximalIdeal A) A]
    (hres : Function.Surjective ((residue A).comp (algebraMap K A))) :
    ∃ r : ℕ, Nonempty (MvPowerSeries (Fin r) K ≃ₐ[K] A) := by sorry
