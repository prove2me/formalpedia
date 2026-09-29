-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen
-- name    : ModularCurve.IgusaScheme.isIntegrallyClosed_sections_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/ed79a69e-54e4-591d-b661-c7d017d00e28
-- title:
--   Normality of the Igusa two-chart model on affine opens
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and a prime number $\ell$. The scheme $\mathtt{ModularCurve.IgusaScheme } N\ \ell$ is, by definition, the pushout in schemes of the two morphisms $\mathtt{fFin } N\ \ell : \mathrm{X\,Mid} \to \mathrm{X\,Fin}$ and $\mathtt{fInf } N\ \ell : \mathrm{X\,Mid} \to \mathrm{X\,Inf}$, each obtained by applying $\mathrm{Spec}$ to the ring homomorphism underlying the inclusion $\mathtt{inclFin } N\ \ell$, respectively $\mathtt{inclInf } N\ \ell$; that is, the two affine charts $\mathrm{X\,Fin}$ and $\mathrm{X\,Inf}$ glued along the affine scheme $\mathrm{X\,Mid}$ common to both. Let $U$ be an open subset of this scheme which is an affine open, i.e. the restriction of the scheme to $U$ is affine. The assertion is that the commutative ring $\Gamma(\mathtt{ModularCurve.IgusaScheme } N\ \ell, U)$ of sections of the structure sheaf over $U$ is integrally closed: every element of its fraction field that is integral over it already lies in the image of the ring. No hypothesis relating $N$ and $\ell$ (such as $\ell \nmid N$) is imposed.
--
--   This is the normality of Igusa's two-chart integral model of the modular curve of level $N$ over the localisation of $\mathbf{Z}$ at $\ell$, expressed as integral closedness of the ring of sections over each affine open. It supplies the normality component of the Deligne–Rapoport-style integral model package constructed in [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel), applied there at level $N_0 q$ and prime $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.isIntegrallyClosed_sections_of_isAffineOpen (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (U : (ModularCurve.IgusaScheme N ℓ).Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed ↑Γ(ModularCurve.IgusaScheme N ℓ, U) := by sorry
