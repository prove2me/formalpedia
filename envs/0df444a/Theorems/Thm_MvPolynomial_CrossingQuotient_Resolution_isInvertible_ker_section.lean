-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section
-- name    : MvPolynomial.CrossingQuotient.Resolution.isInvertible_ker_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/979281e8-de5a-55ca-91f4-21574e7e0d30
-- title:
--   Invertibility of the ideal of a section of the resolution
-- statement:
--   Let $O$ be a commutative ring, $\varpi \in O$ an element lying in the non-zero-divisors of $O$, and $e$ a natural number; let $d$ be a natural number with $0 < d$ and $d < e$, and let $\alpha$ be a unit of $O$. Since $(\varpi\alpha^{-1})\cdot\alpha = \varpi$, the construction `CrossingQuotient.lift` yields the $O$-algebra map $O[x_0,x_1]/(x_0x_1-\varpi) \to O$ sending $x_0 \mapsto \varpi\alpha^{-1}$ and $x_1 \mapsto \alpha$; applying $\operatorname{Spec}$ to its underlying ring homomorphism gives a section $\operatorname{Spec} O \to \operatorname{Spec}\bigl(O[x_0,x_1]/(x_0x_1-\varpi)\bigr)$ of the $(d-1)$-st chart, and this is followed by the structural morphism `Resolution.ι ϖ e ⟨d - 1, _⟩` from that chart into the colimit scheme `Resolution ϖ e` (the index $d-1$ lies in range by $0<d<e$). The assertion is that the kernel ideal sheaf of the resulting morphism $\operatorname{Spec} O \to$ `Resolution ϖ e` satisfies `IsInvertible`, i.e. for every point $x$ of `Resolution ϖ e` there are an affine open $U$ and a section $f \in \Gamma(X,U)$ with $x$ in the basic open set of $f$, together with an element $g$ which is a non-zero-divisor of the ring of sections over the affine basic open set of $f$ and generates the ideal of the kernel ideal sheaf there.
--
--   This records that the ideal sheaf cutting out the section $(x_0,x_1) = (\varpi\alpha^{-1},\alpha)$ of the $(d-1)$-st chart of the explicit resolution of $uv = \varpi^{e}$ is invertible, i.e. Cartier, so that the section meets the special fibre transversally at a smooth point of a single component. It feeds into [`MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable`](thm.html#MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable), where the special fibre of the resolution together with such sections is packaged for use in the regular-model analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.isInvertible_ker_section
    {O : Type u} [CommRing O] (ϖ : O) (e : ℕ) (hϖ : ϖ ∈ nonZeroDivisors O)
    (d : ℕ) (hd0 : 0 < d) (hde : d < e) (α : Oˣ) :
    (Spec.map (CommRingCat.ofHom (CrossingQuotient.lift ϖ (ϖ * ((α⁻¹ : Oˣ) : O)) (α : O)
        (by rw [mul_assoc, Units.inv_mul, mul_one]; rfl)).toRingHom) ≫ Resolution.ι ϖ e ⟨d - 1, by omega⟩).ker.IsInvertible := by sorry
