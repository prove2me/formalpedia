-- Prove2me | Theorems.Thm_ModularCurve_JZero_invariants_le_invariants_of_le
-- name    : ModularCurve.JZero.invariants_le_invariants_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/cfbc974e-a70b-5e40-bef4-6364489b34b2
-- title:
--   Monotonicity of J₀(N)-invariants in the base field
-- statement:
--   Let $N$ be a natural number, assumed nonzero, and let $K \le L'$ be intermediate fields of the extension $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, where $\overline{\mathbb{Q}}$ is Mathlib's algebraic closure of $\mathbb{Q}$. Here `JZero N` is the degree-zero divisor class group `Pic0` of the field extension $\overline{\mathbb{Q}} \subseteq$ `modularFunctionFieldBar N`, that is, the quotient of the additive group of degree-zero divisors by the subgroup of principal divisors, the upper field being the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside $\mathbb{Q}((q))$; it carries a distributive action of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. For an intermediate field $F$, the notation `JZero N ^+ ↥F.fixingSubgroup` denotes the additive subgroup of elements of `JZero N` fixed by every automorphism lying in the fixing subgroup of $F$. The assertion is the inclusion of additive subgroups $$\mathrm{JZero}\,N^{+\,\mathrm{Gal}(\overline{\mathbb{Q}}/K)} \le \mathrm{JZero}\,N^{+\,\mathrm{Gal}(\overline{\mathbb{Q}}/L')}.$$
--
--   This is the functoriality of the groups of points $J_0(N)(K) \subseteq J_0(N)(L')$ of the modular Jacobian under enlarging the field of definition. It is used in the treatment of finite generation of $J_0(N)(K)$ and of the descent of height-two invariants from a larger field to $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_invariants_le_invariants_of_le.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.invariants_le_invariants_of_le (N : ℕ) [NeZero N]
    (K L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L') :
    JZero N ^+ ↥K.fixingSubgroup ≤ JZero N ^+ ↥L'.fixingSubgroup := by sorry
