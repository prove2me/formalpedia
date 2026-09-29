-- Prove2me | Theorems.Thm_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
-- name    : ModularCurve.algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/f550f205-430d-5c64-bc25-bead52104ad2
-- title:
--   Integrality of the integral closure of k[jmath̄] over C
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a positive integer $N$, and a field $k$ of characteristic $q$, together with a surjective ring homomorphism $\mathrm{red}\colon A \to k$ and an intermediate field $K$ of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$. Write $F =$ `modularFunctionFieldC k N` for the subfield of the Laurent series field $k((q))$ generated over $k$ by $\bar\jmath =$ `jqModC k` and by its $N$-th $q$-expansion rescaling `jqNModC k N`, let $\bar\jmath =$ `jGeomGen k N` denote the first of these two generators regarded as an element of $F$, and let $\mathfrak D$ be the integral closure of the $k$-subalgebra $k[\bar\jmath] \subseteq F$ in $F$, viewed as a subring. Let $C$ be a commutative ring and $g\colon C \to \mathfrak D$ a ring homomorphism such that: (i) for every $a$ in `coeffSubring A K` $= A \cap K$ (the intersection of the underlying subrings of $A$ and of $K$ inside $\overline{\mathbb Q}$) there is $c \in C$ with $g(c)$ equal, in $F$, to the image of $\mathrm{red}(a)$ under the structure map $k \to F$; and (ii) there are $c \in C$ and an integer $n > 0$ with $g(c) = \bar\jmath^{\,n}$ in $F$. Then $\mathfrak D$, made into a $C$-algebra via $g$, is integral over $C$: every element of $\mathfrak D$ satisfies a monic polynomial with coefficients in the image of $g$.
--
--   This is the integrality input for lying-over/going-up arguments between a ring of functions defined over a number field and the normal affine chart ring $\mathfrak D$ of a component of the characteristic-$q$ special fibre: it shows that $\mathfrak D$ is integral over any ring mapping into it whose image contains the reduced constants coming from $A \cap K$ and some positive power of $\bar\jmath$. It is cited by the two prolongation-tuple statements comparing values of elements of the $j$-integral closure under the first and second residue maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.algebra_isIntegral_integralClosure_adjoin_jGeomGen_of_exists_apply_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hred : Function.Surjective red)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {C : Type*} [CommRing C]
    (g : C →+* ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring))
    (hconst : ∀ a : ↥(coeffSubring A K), ∃ c, ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (NodeLocalized.redRestrict red K a))
    (hj : ∃ c, ∃ n : ℕ, 0 < n ∧ ((g c : ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring)) : ↥(modularFunctionFieldC k N)) = jGeomGen k N ^ n) :
    @Algebra.IsIntegral C ↥((integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)).toSubring) _ _ g.toAlgebra := by sorry
