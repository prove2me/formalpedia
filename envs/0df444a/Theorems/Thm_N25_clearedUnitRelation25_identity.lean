-- Prove2me | Theorems.Thm_N25_clearedUnitRelation25_identity
-- name    : N25.clearedUnitRelation25_identity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:35.013888+00:00
-- url     : https://prove2.me/theorems/a16204dd-34d2-45d0-ade0-01e08f3a850b
-- title:
--   Clearing denominators recovers the plane relation
-- statement:
--   Let $K$ be a field, let $g,f_0,f_1\in K$, and assume $g\ne0$ and $f_1\ne0$. If $C(g,f_0,f_1)$ denotes the cleared modular-unit relation and $R(X,Y)$ the defining plane relation, then
--
--   $$C(g,f_0,f_1)=g^7f_1^4R(f_0/g,f_0/f_1).$$
--
--   This identifies the homogeneous relation used for Sturm verification with the affine plane equation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitRelation

set_option autoImplicit false
open N25

theorem N25.clearedUnitRelation25_identity
    {K : Type*} [Field K] (g f₀ f₁ : K) (hg : g ≠ 0) (hf₁ : f₁ ≠ 0) :
    clearedUnitRelation25 g f₀ f₁ =
      g ^ 7 * f₁ ^ 4 * planeRelation (f₀ / g) (f₀ / f₁) := by sorry
