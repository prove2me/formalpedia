-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rigidity_radical_orbit_bound
-- name    : OAI.ComplexCancellation.Rigidity.radical_orbit_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:42:58.07626+00:00
-- url     : https://prove2.me/theorems/07ed42b3-98f8-4a56-9228-bc55f3b396da
-- title:
--   Degree bound for the radical of $d^2\cdot a^2u^3\cdot(-n)$
-- statement:
--   Let $k$ be a field. For $g\in k[X]$ let $\operatorname{rad}(g)$ denote the radical of $g$: the product of the distinct monic irreducible polynomials dividing $g$, so that $\operatorname{rad}(g)=1$ for a nonzero constant $g$, and by convention $\operatorname{rad}(0)=1$. Then for all polynomials $a,d,u,n\in k[X]$,
--
--   $$\deg\operatorname{rad}\bigl(d^2\cdot a^2u^3\cdot(-n)\bigr)\le\deg d+\deg a+\deg u+\deg n .$$
--
--   The radical counts each irreducible factor only once, so the exponents $2$, $2$ and $3$ disappear from the bound. This is the upper bound that is combined with the Mason–Stothers inequality for the triple $(d^2,\ a^2u^3,\ -n)$ in the proof that polynomial solutions of $d^2+a^2u^3=n$ with $\deg n\le1$ are constant.
--
--   **Formalization Note** $\operatorname{rad}$ is Mathlib's `UniqueFactorizationMonoid.radical`, the product of the normalized prime factors (monic irreducible factors in $k[X]$), with `radical 0 = 1`. The degree is `natDegree`, for which the zero polynomial has degree $0$; if one of $a,d,u,n$ is zero the inequality holds trivially. A `DecidableEq k` instance is assumed for the radical.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Rigidity.lean#L45-L71

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation

open OAI OAI.ComplexCancellation
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain
variable {k : Type*} [Field k]

theorem OAI.ComplexCancellation.Rigidity.radical_orbit_bound [DecidableEq k] (a d u n : k[X]) :
    (radical (d ^ 2 * (a ^ 2 * u ^ 3) * (-n))).natDegree ≤
    d.natDegree + a.natDegree + u.natDegree + n.natDegree := by sorry
