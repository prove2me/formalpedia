-- Prove2me | Theorems.Thm_LeanEval_AlgebraicGeometry_Faltings_finite_setOf_place_notMem
-- name    : LeanEval.AlgebraicGeometry.Faltings.finite_setOf_place_notMem
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T01:24:14.804037+00:00
-- url     : https://prove2.me/theorems/5bad30dc-7d88-4bd8-8d61-70ec6d088bd6
-- title:
--   Finitely many poles: an element of a function field lies in all but finitely many places
-- statement:
--   An element of an algebraic function field of one variable has only finitely many poles (Stichtenoth, Corollary 1.3.4).
--
--   Let $K$ be a field and $F$ a field carrying a $K$-algebra structure. Assume $F$ is an **algebraic function field of one variable over $K$ with a chosen structure map**: $F$ is an algebra over the rational function field $K(X)$, the tower $K \to K(X) \to F$ is a scalar tower, and $F$ is finite-dimensional over $K(X)$. A **place** of $F/K$ is a proper $K$-subalgebra $\mathcal O_v \subseteq F$ that is a valuation subring, so that for every $x \in F$ either $x \in \mathcal O_v$ or $x^{-1} \in \mathcal O_v$. Write $\operatorname{Place}(F/K)$ for the type of places.
--
--   For every $x \in F$, the set of places at which $x$ has a pole is finite:
--
--   $$\{\, v \in \operatorname{Place}(F/K) \;:\; x \notin \mathcal O_v \,\}\ \text{is finite.}$$
--
--   No hypothesis is placed on $K$ beyond being a field: it need not be perfect, nor finite, nor the full constant field of $F/K$. The element $x$ is arbitrary; if $x$ is algebraic over $K$ the set is empty, and the assertion is that in all cases only finitely many places fail to contain $x$. No bound on the number of poles is asserted.
--
--   This is the statement that makes the divisor of a nonzero function a finite object, and it is the proof obligation behind the diagonal embedding $F \to \mathcal A_F$ of a function field into its adele ring: the constant family $(x)_v$ is an adele precisely because $x$ lies in $\mathcal O_v$ for all but finitely many $v$. The genus used in Faltings' theorem is defined from that diagonal, so this corollary is a prerequisite for even stating the companion goal.
--
--   **Formalization Note.** This is the first hole of the LeanEval problem `faltings`, with the benchmark's binders preserved: `K` is explicit, `F` implicit, the instance arguments are `[Field K] [Field F] [Algebra K F] [BundledFunctionField K F]`, and `x : F` is explicit. Finiteness is `Set.Finite` on a set of places, and membership `x ∉ v` is membership in the carrier of the place via its `SetLike` instance. The place type and `BundledFunctionField` come from the mission's definition layer; only the benchmark marker attribute and its import are omitted.
-- source:
--   LeanEval benchmark problem `faltings`, first hole `finite_setOf_place_notMem` (lines 62–66), https://github.com/leanprover/lean-eval/blob/bcc142463a0530038f12e8f1c1e9cce78e129f0a/LeanEval/AlgebraicGeometry/Faltings.lean#L62-L66 ; mirrored verbatim in AxiomMath/Mordell, `Mordell/LeanEval/Faltings.lean` (lines 122–128), https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/LeanEval/Faltings.lean#L122-L128 . Mathematical source: H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254, 2009, Corollary 1.3.4, https://doi.org/10.1007/978-3-540-77086-4 .

import Mathlib
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Places

namespace LeanEval.AlgebraicGeometry.Faltings

theorem finite_setOf_place_notMem (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]
    [BundledFunctionField K F] (x : F) :
    {v : Place K F | x ∉ v}.Finite := by sorry

end LeanEval.AlgebraicGeometry.Faltings
