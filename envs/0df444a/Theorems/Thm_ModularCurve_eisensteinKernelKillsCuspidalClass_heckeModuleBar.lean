-- Prove2me | Theorems.Thm_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar
-- name    : ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/973c15bd-ba2b-5b1b-a062-cc9b514abcee
-- title:
--   Eisenstein kernel annihilates the cuspidal class on J₀(p)
-- statement:
--   Let $p$ be a prime. Write $J =$ `JZero p` for the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the modular function field of level $p$ over $\overline{\mathbb{Q}}$, and let $c =$ `cuspidalClass p` be the class of the degree-zero divisor $(\text{cusp }0) - (\text{cusp }\infty)$. For each prime $\ell$, `heckeOperatorBar p ℓ` is the $\mathbb{Z}$-linear endomorphism of $J$ induced by the divisorial Hecke operator at $\ell$. Three hypotheses are assumed: (i) these endomorphisms commute pairwise; (ii) for every prime $\ell \neq p$ one has $T_\ell c = (1+\ell)\,c$; (iii) at $\ell = p$ one has $T_p c = c$. Endow $J$ with the action of $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ given by `heckeModuleBar p`, which, since the operators commute, is the action in which $X_\ell$ acts as `heckeOperatorBar p ℓ`. The conclusion is `EisensteinKernelKillsCuspidalClass p (heckeModuleBar p)`: every $t \in \mathbb{T}$ for which there exists $i$ in the Eisenstein ideal `eisensteinIdeal p` with $(1+i)t$ annihilating all of $J$ satisfies $t \cdot c = 0$.
--
--   This is the formal counterpart of Mazur's statement that the Eisenstein ideal, and more precisely the larger kernel ideal $\{t : (1+i)t \text{ kills } J \text{ for some } i \text{ in the Eisenstein ideal}\}$, annihilates the cuspidal divisor class on $J_0(p)$; the hypotheses are exactly the Eisenstein eigenvalue relations $T_\ell c = (1+\ell)c$ for $\ell \neq p$ and $T_p c = c$, together with commutativity of the operators. It is used in turn by [`ModularCurve.heckeOperatorBar_cuspidalClass`](thm.html#ModularCurve.heckeOperatorBar_cuspidalClass) and [`ModularCurve.heckeOperatorBar_cuspidalClass_self`](thm.html#ModularCurve.heckeOperatorBar_cuspidalClass_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eisensteinKernelKillsCuspidalClass_heckeModuleBar.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.eisensteinKernelKillsCuspidalClass_heckeModuleBar (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p) (hT : ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → heckeOperatorBar p ℓ (cuspidalClass p) = (1 + ℓ : ℤ) • cuspidalClass p) (hU : heckeOperatorBar p ⟨p, Fact.out⟩ (cuspidalClass p) = cuspidalClass p) : EisensteinKernelKillsCuspidalClass p (heckeModuleBar p) := by sorry
