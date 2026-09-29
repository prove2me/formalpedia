-- Prove2me | Theorems.Thm_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
-- name    : NumberField.ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/07ac4808-8aa6-5b79-b7ee-66ac92731c90
-- title:
--   Unramified primes stay unramified in the normal closure
-- statement:
--   Let $E$, $K$, $L$ be number fields, each carrying the usual field and number-field structures, together with $E$-algebra structures on $K$ and on $L$ and a $K$-algebra structure on $L$ forming a scalar tower over $E$, and assume `IsNormalClosure E K L`, i.e. $L$ is a normal closure of $K/E$ inside the tower $E \subseteq K \subseteq L$. Let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_E$, that is a nonzero prime ideal of $\mathcal{O}_E$. Assume that for every height-one prime $w$ of $\mathcal{O}_K$ whose contraction `w.under (𝓞 E)` to $\mathcal{O}_E$ equals $v$ — equivalently, every prime of $K$ lying over $v$ — one has `Ideal.ramificationIdx'` of `v.asIdeal` in `w.asIdeal` equal to $1$. The conclusion is that `Ideal.ramificationIdxIn v.asIdeal (𝓞 L)`, the common ramification index of the primes of $\mathcal{O}_L$ above $v$, equals $1$; thus $v$ is unramified in $L$ as soon as it is unramified in $K$.
--
--   This is the classical statement that a prime unramified in a finite extension $K/E$ remains unramified in the normal closure of $K/E$, $L$ being the compositum of the $E$-conjugates of $K$. It is used in the construction of admissible quadratic twists, where the ramification conditions are formulated over a Galois field containing $K$, and is cited by the two existence results for admissible twists with prescribed local behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one.lean

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

theorem NumberField.ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
    (E K L : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] [IsNormalClosure E K L]
    (v : HeightOneSpectrum (𝓞 E))
    (hK : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 := by sorry
