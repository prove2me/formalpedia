-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
-- name    : LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a0585921-bd33-540a-9d27-d55acc18be08
-- title:
--   Norm surjects onto higher unit groups when e=1
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_E$, and let $w$ be an extension of $v$ to $\mathcal{O}_M$, that is, a height-one prime of $\mathcal{O}_M$ whose contraction to $\mathcal{O}_E$ is $v$. Assume that the ramification index $e$ of $w$ over $v$, given by `ramificationIdx'`, equals $1$, and let $m$ be a natural number. For a number field $F$, a height-one prime $u$ of $\mathcal{O}_F$ and $n \in \mathbb{N}$, the set `higherUnitsAt F u n` consists of those units $x$ of the completion $F_u$ with $\mathrm{Valued.v}(x) = 1$ and, when $n \neq 0$, additionally $\mathrm{Valued.v}(x - 1) \le \exp(-n)$ in the value group; thus for $n = 0$ it is the full unit group of the valuation ring, and for $n \ge 1$ it is the group of units congruent to $1$ modulo the $n$-th power of the maximal ideal. The assertion is that the image of `higherUnitsAt M w.1 m` under the map on unit groups induced by the algebra norm $\mathrm{Algebra.norm}$ of $M_w$ over $E_v$ is exactly `higherUnitsAt E v m`.
--
--   This is the classical surjectivity of the local norm on higher unit groups for an unramified extension of local fields, $N_{M_w/E_v}(U_w^{(m)}) = U_v^{(m)}$ for all $m \ge 0$. It is used to transfer conductor-exponent information along the norm, to identify the image of the norm map on units in terms of divisibility by the inertia degree, and in the analysis of local behaviour at places with $e = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.image_norm_higherUnitsAt_eq_of_ramificationIdx_eq_one
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) (m : ℕ) :
    (Units.map (Algebra.norm (v.adicCompletion E))) '' LanglandsTunnell.TateLocal.higherUnitsAt M w.1 m =
      LanglandsTunnell.TateLocal.higherUnitsAt E v m := by sorry
