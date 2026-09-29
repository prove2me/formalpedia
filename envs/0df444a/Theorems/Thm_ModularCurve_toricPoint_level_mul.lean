-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_level_mul
-- name    : ModularCurve.toricPoint_level_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/31531fba-6a0f-5016-b83a-632a30fc868b
-- title:
--   Toric point at level ap is the qᵃ-expansion
-- statement:
--   Let $K$ be a field, let $p$ and $a$ be natural numbers with $a \neq 0$ (no condition is imposed on $p$, which may be $0$), and let $c \in K$. For a natural number $n$, `toricPoint K n c` is the pair of Laurent series over $K$ obtained by viewing as Hahn series the two power series whose $m$-th coefficients are: for the first coordinate, $c/(1-c)^2$ when $m = 0$ and $\sum_{d \mid m,\ n \mid d} (m/d)\,(c^{m/d} + c^{-m/d}) - 2\,[\,n \mid m\,]\sum_{e \mid m/n} e$ when $m \neq 0$; for the second coordinate, $c^2/(1-c)^3$ when $m = 0$ and $\sum_{d \mid m,\ n \mid d}\big(\binom{m/d}{2} c^{m/d} - \binom{m/d+1}{2} c^{-m/d}\big) + [\,n \mid m\,]\sum_{e \mid m/n} e$ when $m \neq 0$ (all divisor sums over the divisors of the indicated natural number, and inverses taken in $K$). Here `qExpand K a` is the ring homomorphism on Laurent series that moves the coefficient in degree $g$ to degree $a g$ and is zero in degrees not divisible by $a$, i.e. the substitution $q \mapsto q^a$. The assertion is the equality of pairs $$\mathtt{toricPoint}\,K\,(a p)\,c = \big(\mathtt{qExpand}\,K\,a\,(\mathtt{toricPoint}\,K\,p\,c)_1,\ \mathtt{qExpand}\,K\,a\,(\mathtt{toricPoint}\,K\,p\,c)_2\big),$$ so that both coordinates of the toric point at level $a p$ with parameter $c$ are the $q^a$-expansions of the corresponding coordinates at level $p$ with the same parameter $c$; note that no power of $c$ is introduced by the change of level.
--
--   This is the level-change (expansion) law for the distinguished toric points of the Tate curve: the series attached to level $ap$ is obtained from the level-$p$ series by the substitution $q \mapsto q^a$, the toric counterpart of the corresponding law for the non-toric torsion points. It is used throughout the construction of modular forms with prescribed $q$-expansions at composite level, for instance in the statements producing forms whose $q$-expansions are built from products of values of `toricPoint`, and it allows an on-curve identity verified at level one to be transported to every level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_level_mul.lean

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries

theorem ModularCurve.toricPoint_level_mul (K : Type*) [Field K] (p a : ℕ) [NeZero a] (c : K) :
    toricPoint K (a * p) c =
      (qExpand K a (toricPoint K p c).1, qExpand K a (toricPoint K p c).2) := by sorry
