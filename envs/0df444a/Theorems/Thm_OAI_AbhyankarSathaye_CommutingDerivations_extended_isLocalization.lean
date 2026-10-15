-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_extended_isLocalization
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:42:49.5855+00:00
-- url     : https://prove2.me/theorems/b688b608-f055-4d08-ac42-6795edc0d0e2
-- title:
--   Inverting $F_n+1$ in $\mathbb{C}[X_0,\dots,X_{n-1}]$ gives a polynomial ring over the four-variable localization
-- statement:
--   Fix $n\ge4$ and let $A_n=\mathbb{C}[X_0,\dots,X_{n-1}]$. Let $R=\mathbb{C}[X_0,X_1,X_2,X_3]$ and, with $h=X_0$, $u=X_1$, $v=X_2$, $w=X_3$, $x=u^3+hv$, $y=-u^2+hw$, $s=2u^3v+3u^4w+h(v^2-3u^2w^2)+h^2w^3$ and $p=-2s^2x+3sy^2-3s^3y$, put $F=h-p-1\in R$. Let $F_n\in A_n$ be the same polynomial regarded as an element of $A_n$ (it involves only $X_0,\dots,X_3$).
--
--   Let $R_{F+1}=R[(F+1)^{-1}]$ be the localization of $R$ away from $F+1$, let $B_n=R_{F+1}[Y_0,\dots,Y_{n-5}]$ be the polynomial ring in $n-4$ variables over it (so $B_4=R_{F+1}$), and let $\iota_n:A_n\to B_n$ be the $\mathbb{C}$-algebra homomorphism with $\iota_n(X_j)=X_j/1$ (a constant polynomial) for $0\le j\le 3$ and $\iota_n(X_{4+i})=Y_i$ for $0\le i<n-4$. Then, with the $A_n$-algebra structure given by $\iota_n$, the ring $B_n$ is a localization of $A_n$ away from $F_n+1$:
--
--   $$
--   B_n\;\cong\;A_n\bigl[(F_n+1)^{-1}\bigr]\qquad\text{via }\iota_n .
--   $$
--
--   Explicitly: $\iota_n(F_n+1)$ is a unit of $B_n$; every element of $B_n$ has the form $\iota_n(a)\,\iota_n(F_n+1)^{-k}$ with $a\in A_n$ and $k\ge0$; and $\iota_n(a)=\iota_n(b)$ holds exactly when $(F_n+1)^k a=(F_n+1)^k b$ for some $k\ge0$.
--
--   This gives a concrete model of the localization of the $n$-variable polynomial ring at $F_n+1$: it is a polynomial ring over the four-variable localization $R_{F+1}$, so explicit coordinates on $R_{F+1}$ extend to every dimension $n\ge4$ by adjoining the extra variables unchanged. It provides the localization structure used to clear denominators of derivations and to compute the kernel intersection in dimension $n$.
--
--   **Formalization Note** In Lean, $B_n$ is `ExtendedLocalizedAmbient n`, defined as `MvPolynomial (Fin (n-4)) LocalizedAmbient` with `LocalizedAmbient = Localization.Away (F + 1)`, and $F_n$ is `extendedF hn`. The algebra structure is not a global instance; the statement introduces it with `letI := extendedAlgebra hn`, whose structure map `extendedLocMap hn` is the splitting isomorphism `splitAmbient hn` followed by the coefficientwise localization map. The conclusion is `IsLocalization.Away (extendedF hn + 1) (ExtendedLocalizedAmbient n)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/AlgebraicGeometry/CommutingDerivations/ExtendedLocalization.lean#L45-L60

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

open OAI OAI.AbhyankarSathaye OAI.AbhyankarSathaye.CommutingDerivations
open MvPolynomial

theorem OAI.AbhyankarSathaye.CommutingDerivations.extended_isLocalization {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n) := by sorry
