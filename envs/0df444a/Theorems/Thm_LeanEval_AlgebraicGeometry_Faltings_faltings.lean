-- Prove2me | Theorems.Thm_LeanEval_AlgebraicGeometry_Faltings_faltings
-- name    : LeanEval.AlgebraicGeometry.Faltings.faltings
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T01:48:33.663828+00:00
-- url     : https://prove2.me/theorems/9aa2cb64-e17e-4567-83de-4a4686094eef
-- title:
--   Faltings' theorem: finitely many degree-one places in genus $\ge 2$ over a number field
-- statement:
--   Faltings' theorem (the Mordell conjecture), in the function-field form fixed by the LeanEval benchmark: a function field of genus at least two over a number field has only finitely many places of degree one.
--
--   Let $K$ be a **number field**, that is, a finite extension of $\mathbb Q$, and let $F$ be a field carrying a $K$-algebra structure. Assume $F$ is an **algebraic function field of one variable over $K$ with a chosen structure map**: $F$ is an algebra over the rational function field $K(X)$, the tower $K \to K(X) \to F$ is a scalar tower, and $F$ is finite-dimensional over $K(X)$. Equivalently, $F$ is the function field of a smooth projective geometrically integral curve over $K$.
--
--   A **place** of $F/K$ is a proper $K$-subalgebra $\mathcal O_v \subseteq F$ that is a valuation subring; it is a local ring with maximal ideal $\mathfrak m_v$ and **residue field** $\kappa(v) = \mathcal O_v/\mathfrak m_v$, an extension field of $K$. The place has **degree one** when $\kappa(v)$ is one-dimensional over $K$; degree-one places are exactly the $K$-rational points of the curve.
--
--   The **genus** is the adelic quantity $g(F/K) = \dim_K \mathcal A_F / (\mathcal A_F(0) + F)$, where $\mathcal A_F$ is the adele ring of $F/K$, $\mathcal A_F(0)$ the integral adeles, and $F$ is embedded diagonally.
--
--   If $g(F/K) \ge 2$, then
--
--   $$\{\, v \in \operatorname{Place}(F/K) \;:\; \dim_K \kappa(v) = 1 \,\}\quad\text{is finite.}$$
--
--   The hypothesis is a lower bound on the genus, with no upper bound and no restriction on the curve beyond smoothness and geometric integrality, which are built into the function-field hypothesis. The base field $K$ is an arbitrary number field, not only $\mathbb Q$. The conclusion is finiteness of the set of degree-one places; no explicit bound, and no effectiveness, is asserted. If $K$ is not the full constant field of $F/K$ the set is empty, since every place contains the full constant field; that case is included, not excluded.
--
--   This is the finiteness theorem for rational points on curves of general type, conjectured by Mordell in 1922 and proved by Faltings in 1983, with later proofs by Vojta and Bombieri. It is the dividing line between curves whose rational points can be infinite (genus $0$ and $1$) and those where they cannot, and it is the starting point for the effective and higher-dimensional refinements of Diophantine geometry.
--
--   **Formalization Note.** This is the second hole of the LeanEval problem `faltings`, with the benchmark's binders preserved: `K` and `F` explicit, `[Field K] [Field F] [Algebra K F] [NumberField K] [BundledFunctionField K F]`, and the hypothesis `(h : 2 ≤ genus K F)` on the mission's adelic `genus`. Degree one is written as `Module.rank K (IsLocalRing.ResidueField v) = 1`, an equality of cardinals, exactly as in the benchmark, and finiteness is `Set.Finite`. The places, adeles and genus come from the mission's definition layer; only the benchmark marker attribute and its import are omitted.
-- source:
--   LeanEval benchmark problem `faltings`, second hole `faltings` (lines 122–129), https://github.com/leanprover/lean-eval/blob/bcc142463a0530038f12e8f1c1e9cce78e129f0a/LeanEval/AlgebraicGeometry/Faltings.lean#L122-L129 ; mirrored verbatim in AxiomMath/Mordell, `Mordell/LeanEval/Faltings.lean` (lines 293–302), https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/LeanEval/Faltings.lean#L293-L302 . Mathematical sources: G. Faltings, Endlichkeitssätze für abelsche Varietäten über Zahlkörpern, Invent. Math. 73 (1983), 349–366, https://doi.org/10.1007/BF01388432 ; E. Bombieri, The Mordell conjecture revisited, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 17 (1990), 615–640 ; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254, 2009, Definitions 1.1.4, 1.1.8, 1.5.2, 1.5.3 and Corollary 1.5.5 (genus), https://doi.org/10.1007/978-3-540-77086-4 .

import Mathlib
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Places
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Adeles

namespace LeanEval.AlgebraicGeometry.Faltings

theorem faltings (K F : Type*) [Field K] [Field F] [Algebra K F] [NumberField K]
    [BundledFunctionField K F] (h : 2 ≤ genus K F) :
    {v : Place K F | Module.rank K (IsLocalRing.ResidueField v) = 1}.Finite := by sorry

end LeanEval.AlgebraicGeometry.Faltings
