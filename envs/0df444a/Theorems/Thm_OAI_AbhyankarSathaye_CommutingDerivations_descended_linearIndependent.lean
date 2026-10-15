-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_descended_linearIndependent
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.descended_linearIndependent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:47:18.97895+00:00
-- url     : https://prove2.me/theorems/30b651b6-a1f2-4f88-b0b5-a36d6adb5cbd
-- title:
--   Denominator-cleared derivations with dual coordinates are linearly independent over the base ring
-- statement:
--   Let $K$ be a commutative ring, $A$ and $L$ commutative $K$-algebras, and $\iota:A\to L$ an injective $K$-algebra homomorphism. Let $c\in A$ be an element such that $\iota(c)$ is a unit of $L$, let $N\in\mathbb{N}$, and let $I$ be a finite index set. Let $(D_i)_{i\in I}$ be $K$-linear derivations of $L$ and $(d_i)_{i\in I}$ be $K$-linear derivations of $A$, and assume:
--
--   1. (descent) $\iota(d_i(a))=\iota(c)^N\,D_i(\iota(a))$ for all $i\in I$ and $a\in A$;
--   2. (the denominator is a constant) $D_i(\iota(c))=0$ for all $i\in I$;
--   3. (dual coordinates) there are elements $t_j\in L$, $j\in I$, with $D_i(t_j)=\delta_{ij}$ (the Kronecker delta) for all $i,j\in I$;
--   4. (fractions) for each $j\in I$ there are $n_j\in\mathbb{N}$ and $r_j\in A$ with $t_j\,\iota(c)^{n_j}=\iota(r_j)$.
--
--   Then the family $(d_i)_{i\in I}$ is linearly independent over $A$ in the $A$-module of $K$-linear derivations of $A$:
--
--   $$
--   \sum_{i\in I}a_i\,d_i=0\ \ \text{with } a_i\in A\quad\Longrightarrow\quad a_i=0\ \text{ for all } i\in I.
--   $$
--
--   Typically $L$ is the localization $A[c^{-1}]$, the $D_i$ are partial derivatives with respect to coordinates $t_j$ of $L$ over a ring of constants containing $\iota(c)$, and the $d_i$ are their restrictions to $A$ after clearing denominators. The theorem transfers the evident independence of coordinate partials to the descended derivations, without any domain hypothesis on $A$.
--
--   **Formalization Note** The Kronecker delta is written `if i = j then 1 else 0`, which is why `[DecidableEq I]` is assumed alongside `[Fintype I]`. The conclusion is Mathlib's `LinearIndependent A d`, for the natural $A$-module structure on `Derivation K A A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/DescentFamily.lean#L58-L91

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Identities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBezout
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_LiftingIdentities__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Reconstruction__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Quotient__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationSetup
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_CoefficientInstances
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterBridge
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_LocalizationEquivalence
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Lifting__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Plane__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Presentation__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Fiber__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_CriticalPoint__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_AbhyankarSathaye_Stabilization__CommutingDerivations
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedLocalization
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedParameterRetraction
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ConcreteKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_ExtendedKernelIntersection
import Definitions.Def_OAI_AlgebraicGeometry_CommutingDerivations_DerivationOperations

open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
variable {K A L I : Type*} [CommRing K] [CommRing A] [CommRing L]
  [Algebra K A] [Algebra K L]

theorem OAI.AbhyankarSathaye.CommutingDerivations.descended_linearIndependent [Fintype I] [DecidableEq I]
    (ι : A →ₐ[K] L) (hinj : Function.Injective ι) (c : A)
    (hu : IsUnit (ι c)) (N : ℕ)
    (D : I → Derivation K L L) (d : I → Derivation K A A)
    (hdesc : ∀ i a, ι (d i a) = (ι c)^N * D i (ι a))
    (hfix : ∀ i, D i (ι c) = 0)
    (t : I → L) (ht : ∀ i j, D i (t j) = if i = j then 1 else 0)
    (hfrac : ∀ j, ∃ (n : ℕ) (r : A), t j * (ι c)^n = ι r) :
    LinearIndependent A d := by sorry
