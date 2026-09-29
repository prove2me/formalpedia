-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_finrank_eq_of_pinned_of_flat_morphismRestrict
-- name    : ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/bb5f386a-dbdd-56be-b0c8-5da5996ce64e
-- title:
--   Rank of a pinned flat degeneracy map of Igusa schemes
-- statement:
--   Fix natural numbers $M$, $q$, $\ell$ with $M \neq 0$ and $q$, $\ell$ prime, and $M' \neq 0$ with $M' = M\ell$. Write $R = \mathbb{Z}_{(q)}$ for [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $q$. Let $\pi$ be a morphism $\mathrm{IgusaScheme}\,M'\,q \to \mathrm{IgusaScheme}\,M\,q$ together with the identity $\pi \text{ followed by } \mathrm{igusaTo}\,M\,q = \mathrm{igusaTo}\,M'\,q$ (a morphism over $\operatorname{Spec} R$), assumed finite. Let $\iota$ be an $R$-algebra map from `chartAlgFin M q` to `chartAlgFin M' q`, i.e. between the subalgebras of integral elements over $R[j]$ inside the fields $F_N = \mathbb{Q}(\{q\text{-expansions } j(q^d) : d \mid N\}) \subseteq \mathbb{Q}(\!(q)\!)$. Let $e$ be a ring endomorphism of $\mathbb{Q}(\!(q)\!)$ which is either the identity or `qExpand ℚ ℓ` (multiplication by $\ell$ on Laurent exponents), and assume $\iota$ acts on Laurent series through $e$: the series of $\iota b$ equals $e$ of the series of $b$ for all $b$. Assume the chart pinning $\mathrm{\iota Fin}\,M'\,q$ followed by $\pi$ equals $\operatorname{Spec}(\iota)$ followed by $\mathrm{\iota Fin}\,M\,q$. Finally let $U$ be an open of $\mathrm{IgusaScheme}\,M\,q$ with $\pi \mid_U$ flat, and $y \in U$. Then $\pi$ has rank $\ell$ at $y$ if $\ell \mid M$, and $\ell + 1$ otherwise.
--
--   This is the arithmetic-geometric form of the index computation $[\Gamma_0(M) : \Gamma_0(M\ell)] = \ell + 1 - [\ell \mid M]$: the degree of either of the two standard degeneracy maps $X_0(M\ell) \to X_0(M)$, realised here on the Igusa models over $\mathbb{Z}_{(q)}$ and read off as the local rank of a finite flat morphism. It supplies the rank clauses of [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair), which packages the pair of degeneracy maps used in the Hecke theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_finrank_eq_of_pinned_of_flat_morphismRestrict.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve.IgusaScheme
open ModularCurve

theorem ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict
    (M q ℓ : ℕ) [NeZero M] [Fact q.Prime] [Fact ℓ.Prime] (M' : ℕ) [NeZero M'] (hM' : M' = M * ℓ)
    (π : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q)) [IsFinite π.1]
    (ι : ↥(IgusaScheme.chartAlgFin M q) →ₐ[↥(GaloisRep.ratLocalizedAt q)] ↥(IgusaScheme.chartAlgFin M' q))
    (e : LaurentSeries ℚ →+* LaurentSeries ℚ) (he : e = RingHom.id _ ∨ e = qExpand ℚ ℓ)
    (hι : ∀ b, (((ι b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        e ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (hπ : IgusaScheme.ιFin M' q ≫ π.1 = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ IgusaScheme.ιFin M q)
    (U : (IgusaScheme M q).Opens) [Flat (π.1 ∣_ U)] (y : ↥(IgusaScheme M q)) (hy : y ∈ U) :
    π.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1) := by sorry
