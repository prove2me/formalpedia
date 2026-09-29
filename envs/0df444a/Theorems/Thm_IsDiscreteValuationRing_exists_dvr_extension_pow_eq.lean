-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_dvr_extension_pow_eq
-- name    : IsDiscreteValuationRing.exists_dvr_extension_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c0ec4b4b-146d-56cd-a21a-424efbb9db22
-- title:
--   DVR extension containing an n-th root of π
-- statement:
--   Let $R_0$ be a discrete valuation ring which is a commutative domain, and let $K$ be a field equipped with an $R_0$-algebra structure making it a fraction field of $R_0$ (both in the same universe). Let $n$ be a natural number whose image $(n : R_0)$ is a unit of $R_0$ and which satisfies $n > 0$, and let $\pi \in R_0$ be nonzero. Then there exist a field $K'$ with an algebra structure over $K$, a commutative domain $A'$ which is a discrete valuation ring, an algebra structure of $A'$ on $K'$ exhibiting $K'$ as a fraction field of $A'$, and a ring homomorphism $f : R_0 \to A'$, such that: (i) the composite $f$ followed by $\mathrm{algebraMap}\,A'\,K'$ equals the composite $\mathrm{algebraMap}\,R_0\,K$ followed by $\mathrm{algebraMap}\,K\,K'$, as ring homomorphisms $R_0 \to K'$; (ii) for every $x \in K$, if the image of $x$ in $K'$ lies in the image of $A'$, then $x$ lies in the image of $R_0$ in $K$; and (iii) there is $\varpi \in A'$ whose image in $K'$ satisfies $\varpi^n = \pi$, the right-hand side meaning the image of $\pi$ under $R_0 \to K \to K'$. No finiteness or algebraicity of $K'/K$ is asserted, only the three displayed conditions.
--
--   This is the standard construction of a discrete valuation ring extension, inside an extension of the fraction field, in which a prescribed nonzero element acquires an $n$-th root, together with the statement that the extension is "faithful" over $R_0$ in the sense that elements of $K$ integral over the new ring already lie in $R_0$ (so in particular units of $A'$ lying in $K$ come from units of $R_0$). It is used in the study of Weierstrass models over a discrete valuation ring, where passing to such an extension makes a twist by an $n$-th root of a discriminant-type quantity available while allowing unit statements to be read back in $K$; it is cited by [`WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range`](thm.html#WeierstrassCurve.exists_variableChange_smul_eq_map_of_isLevelPStructure_of_jOfUnit_mem_range).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_dvr_extension_pow_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsDiscreteValuationRing.exists_dvr_extension_pow_eq
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (n : ℕ) (hn : IsUnit ((n : ℕ) : R₀)) (hn0 : 0 < n) (π : R₀) (hπ : π ≠ 0) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K')
      (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
      (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
      (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
      ∃ ϖ : A', (algebraMap A' K' ϖ) ^ n = algebraMap K K' (algebraMap R₀ K π) := by sorry
