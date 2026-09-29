-- Prove2me | Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
-- name    : ModularCurve.atkinLehnerInvolutionFull_apply_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/ad61fe47-08d6-5b87-9ab8-f549ba7842c4
-- title:
--   The partial Atkin–Lehner automorphism wₚ is an involution
-- statement:
--   Let $N$ be a non-zero natural number and $p$ a prime with $p \nmid N$, and let $F =$ `modularFunctionFieldFull (N * p)` be the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (Laurent series over $\mathbb{Q}$) obtained by adjoining to $\mathbb{Q}$ the set of all $q$-expansions $\mathrm{qExpand}\,\mathbb{Q}\,d\,j$, i.e. $j(q^{d})$, for non-zero divisors $d$ of $Np$. Let $w_p =$ `atkinLehnerInvolutionFull N p` be the $\mathbb{Q}$-algebra automorphism of $F$ defined by choice: it is some $\mathbb{Q}$-algebra automorphism $\sigma$ of $F$ satisfying `IsAtkinLehnerAutFull N p`, namely $\sigma(j(q^{d})) = j(q^{dp})$ and $\sigma(j(q^{dp})) = j(q^{d})$ for every non-zero divisor $d$ of $N$, if such an automorphism exists, and the identity automorphism otherwise. The assertion is that for every $x \in F$ one has $w_p(w_p(x)) = x$; that is, $w_p$ is an involution of $F$.
--
--   This is the partial Atkin–Lehner involution $w_p$ at level $Np$ in its $q$-expansion presentation of the function field of $X_0(Np)$ over $\mathbb{Q}$, and the statement records that the automorphism selected by the definition really has order dividing $2$. It is used in the construction of the Deligne–Rapoport model packages, in particular when comparing the two valuation subrings (cusps) interchanged by $w_p$ and when identifying stalk maps at the generic point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply.lean

import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.atkinLehnerInvolutionFull_apply_apply (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hpN : ¬ p ∣ N) (x : modularFunctionFieldFull (N * p)) :
    atkinLehnerInvolutionFull N p (atkinLehnerInvolutionFull N p x) = x := by sorry
