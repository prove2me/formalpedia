-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_integer_prime_pow_dvd_of_localization
-- name    : OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:17:09.832994+00:00
-- url     : https://prove2.me/theorems/09d429d4-7023-424e-84fa-16719ccaf126
-- title:
--   Prime-power divisibility descends from the localization at p
-- statement:
--   Let $p$ be prime and let $A$ be the localization of $\mathbb Z$ at the prime ideal $(p)$. For $t\in\mathbb N$ and $x\in\mathbb Z$,
--   $$
--   p^t\mid x\ \text{in }A\quad\Longrightarrow\quad p^t\mid x\ \text{in }\mathbb Z .
--   $$
--
--   Divisibility by powers of $p$ can thus be checked after inverting all integers prime to $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/IntegerLocalDivisibility.lean#L20-L41

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

open OAI OAI.CirculantHadamard
universe uA

theorem OAI.CirculantHadamard.integer_prime_pow_dvd_of_localization
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by sorry
