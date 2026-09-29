-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem
-- name    : ModularCurve.exists_coeffEmb_basis_of_forall_coeffMap_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b1d2eefe-20c6-5b06-ad06-4186c7166292
-- title:
--   Galois descent for stable subspaces of L((q))
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure making it a finite Galois extension of $\mathbb{Q}$, and let $V$ be an $L$-submodule of the Laurent series ring $\mathrm{LaurentSeries}\,L$ which is finite-dimensional over $L$. Assume that $V$ is stable under the coefficientwise Galois action: for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $L$ and every $x \in V$, the series [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) of the underlying ring homomorphism of $\sigma$ applied to $x$ — that is, the Laurent series whose $k$-th coefficient is $\sigma$ of the $k$-th coefficient of $x$ — again lies in $V$. The conclusion asserts the existence of a natural number $n$ and a family $Y : \mathrm{Fin}\,n \to \mathrm{LaurentSeries}\,\mathbb{Q}$ of Laurent series with rational coefficients such that the family of their images under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81), namely the coefficientwise application of $\mathrm{algebraMap}\,\mathbb{Q}\,L$, is $L$-linearly independent and has $L$-span equal to $V$ as a submodule of $\mathrm{LaurentSeries}\,L$. Thus $V$ admits an $L$-basis consisting of series all of whose coefficients are rational.
--
--   This is Galois descent for a finite-dimensional space of $q$-expansions: a $\mathrm{Gal}(L/\mathbb{Q})$-stable $L$-subspace of $L((q))$ is spanned by series with rational coefficients. It is used in the construction of rational bases of spaces of $q$-expansions on modular curves, in particular by [`ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem`](thm.html#ModularCurve.exists_rational_basis_isModPFormFn_of_forall_coeffMap_mem) and by [`ModularCurve.NodeLocalized.exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral`](thm.html#ModularCurve.NodeLocalized.exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffEmb_basis_of_forall_coeffMap_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_coeffEmb_basis_of_forall_coeffMap_mem
    (L : Type*) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (V : Submodule L (LaurentSeries L)) [FiniteDimensional L V]
    (hV : ∀ (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries L), x ∈ V → ModularCurve.coeffMap (σ : L →+* L) x ∈ V) :
    ∃ (n : ℕ) (Y : Fin n → LaurentSeries ℚ),
      LinearIndependent L (fun i => ModularCurve.coeffEmb L (Y i)) ∧
      Submodule.span L (Set.range fun i => ModularCurve.coeffEmb L (Y i)) = V := by sorry
