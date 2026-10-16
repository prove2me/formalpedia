-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rigidity_orbit_coprime
-- name    : OAI.ComplexCancellation.Rigidity.orbit_coprime
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:42:15.417778+00:00
-- url     : https://prove2.me/theorems/1cb26fd6-d14a-4628-9d17-5ec7966a4e5c
-- title:
--   If $d^2+a^2u^3$ is a nonzero polynomial of degree at most one, then $d^2$ and $a^2u^3$ are coprime
-- statement:
--   Let $k$ be a field and let $a,d,u,n\in k[X]$ be polynomials with $n\neq0$ and $\deg n\le1$. If
--
--   $$d^2+a^2u^3=n,$$
--
--   then $d^2$ and $a^2u^3$ are coprime in $k[X]$, that is, there exist $\lambda,\mu\in k[X]$ with
--
--   $$\lambda\,d^2+\mu\,a^2u^3=1 .$$
--
--   No assumption on the characteristic of $k$ is needed. The statement supplies the coprimality hypothesis of the Mason–Stothers theorem for the triple $(d^2,\ a^2u^3,\ -n)$, which is how polynomial solutions of $d^2+a^2u^3=n$ with $n$ of degree at most one are shown to be constant.
--
--   **Formalization Note** Coprimality is Mathlib's `IsCoprime`, i.e. the existence of a Bézout relation as displayed, and $\deg$ is `natDegree`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Rigidity.lean#L27-L43

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

theorem OAI.ComplexCancellation.Rigidity.orbit_coprime {a d u n : k[X]} (hn : n ≠ 0) (hdeg : n.natDegree ≤ 1)
    (heq : d ^ 2 + a ^ 2 * u ^ 3 = n) : IsCoprime (d ^ 2) (a ^ 2 * u ^ 3) := by sorry
