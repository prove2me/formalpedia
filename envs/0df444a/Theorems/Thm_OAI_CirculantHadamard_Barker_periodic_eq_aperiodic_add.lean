-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_Barker_periodic_eq_aperiodic_add
-- name    : OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:16:28.613516+00:00
-- url     : https://prove2.me/theorems/05b6e7d3-d617-4b50-b460-d345b3659509
-- title:
--   Periodic autocorrelation as a sum of two aperiodic ones
-- statement:
--   Let $n\ge1$, $h:\mathbb Z/n\to\mathbb Z$ and $a\ne0$ in $\mathbb Z/n$, with representative $0<a<n$. Write $P(a)=\sum_{j}h_jh_{j-a}$ for the periodic and $A(k)=\sum_{j<n-k}h_jh_{j+k}$ for the aperiodic autocorrelation. Then
--   $$
--   P(a)=A(a)+A(n-a).
--   $$
--
--   For a Barker sequence this bounds every off-peak periodic autocorrelation by $2$ in absolute value.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Barker/Wraparound.lean#L9-L69

import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.Barker
open scoped BigOperators

theorem OAI.CirculantHadamard.Barker.periodic_eq_aperiodic_add {n : ℕ} [NeZero n]
    (h : Fin n → ℤ) (a : Fin n) (_ : a ≠ 0) :
    periodic h a = aperiodic h a.val + aperiodic h (n - a.val) := by sorry
