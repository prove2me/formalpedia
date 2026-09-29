-- Prove2me | Theorems.Thm_ModularCurve_jqN_prime_not_mem_full
-- name    : ModularCurve.jqN_prime_not_mem_full
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/f53dbbb6-357c-503b-9993-e09764b6d02c
-- title:
--   Non-membership of j(qᵖ) in the level-M divisor-expansion field
-- statement:
--   Let $M$ be a nonzero natural number and $p$ a prime not dividing $M$. Work inside the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$, where `jq` is the series $q^{-1}$ times the power series `jNumQ` (the integral numerator series of the $j$-invariant, with coefficients mapped into $\mathbb{Q}$), and for a nonzero $N$ the series `jqN N` is the image of `jq` under the ring homomorphism `qExpand ℚ N`, which multiplies all exponents by $N$, i.e. the substitution $q \mapsto q^N$. Assume that for every nonzero divisor $d$ of $M$ both of the following hold: the degree of $\mathbb{Q}(jq)\bigl(\mathtt{jqN } d\bigr)$ over $\mathbb{Q}(jq)$ equals `dedekindPsi d`, defined as $\sum_{e \mid d,\ e \text{ squarefree}} d/e$; and the field $\mathbb{Q}(jq, \mathtt{jqN } d)$ generated over $\mathbb{Q}$ by the two series coincides with the field generated over $\mathbb{Q}$ by all expansions $\mathtt{jqN } e$ with $e$ a nonzero divisor of $d$. The conclusion is that `jqN p`, the series $j(q^p)$, does not lie in the field generated over $\mathbb{Q}$ by the expansions $\mathtt{jqN } d$ for the nonzero divisors $d$ of $M$.
--
--   This is the base step of the non-membership tower used in the purely algebraic computation of $[\mathbb{Q}(j) (j_N) : \mathbb{Q}(j)] = \psi(N)$, equivalently of the irreducibility of the modular polynomial $\Phi_N$ over $\mathbb{Q}(j)$ and of the description of the function field of $X_0(N)$. It is cited in the inductive construction of irreducible modular polynomial data and in the construction of Atkin–Lehner type automorphisms at a prime away from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.jqN_prime_not_mem_full (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d], Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧ modularFunctionField d = modularFunctionFieldFull d) : jqN p ∉ modularFunctionFieldFull M := by sorry
