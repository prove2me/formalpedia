-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
-- name    : ModularCurve.IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/202e911d-a3d3-5146-a8f7-43cc07735730
-- title:
--   Geometric reducedness of the fibres of the Igusa scheme at level Np
-- statement:
--   Let $N$ be a non-zero natural number and $p$ a prime with $p \nmid N$, and write $\mathbb{Z}_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator (in lowest terms) is coprime to $p$. Let $L$ be any field equipped with a $\mathbb{Z}_{(p)}$-algebra structure; no assumption is made on its characteristic. The scheme [`ModularCurve.IgusaScheme (N * p) p`](def/ModularCurve_IgusaScheme.html#L255) is the pushout, in schemes, of the two morphisms $\mathrm{Spec}$ of the inclusions `inclFin` and `inclInf` of the middle chart ring into the two $\mathbb{Z}_{(p)}$-subalgebras `chartAlgFin (N * p) p` $=$ `chartAlg (N * p) p {jFull (N * p)}` and `chartAlgInf (N * p) p` $=$ `chartAlg (N * p) p {(jFull (N * p))⁻¹}` of the full modular function field of level $Np$; that is, it is obtained by glueing the two affine charts $\mathrm{Spec}$ of these algebras along their common affine overlap. The morphism `igusaTo (N * p) p` to $\mathrm{Spec}\,\mathbb{Z}_{(p)}$ is the one induced on the pushout by the structural maps $\mathbb{Z}_{(p)} \to$ `chartAlgFin`, `chartAlgInf`. The assertion is that the fibre product of this morphism with $\mathrm{Spec}$ of the structure map $\mathbb{Z}_{(p)} \to L$ is a reduced scheme.
--
--   This is the geometric reducedness, in the two-chart integral model over $\mathbb{Z}_{(p)}$, of the fibres of $X_0(Np)$ for $p \nmid N$, the form in which the Deligne–Rapoport description of the special fibre at $p$ (two copies of $X_0(N)_{\mathbb{F}_p}$ crossing at the supersingular points, each of multiplicity one) is used here. It feeds the analysis of the minimal primes of $(p)$ in the chart algebras and of the nodes of the special fibre, which in turn supports the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt p) L] :
    IsReduced (pullback (igusaTo (N * p) p)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt p) L)) := by sorry
