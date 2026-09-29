-- Prove2me | Theorems.Thm_ModularCurve_exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
-- name    : ModularCurve.exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d763b03c-d9a9-502e-aefb-1fb7be94618e
-- title:
--   Order homomorphism taking the Hasse root function to value coprime to p-1
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $\kappa$ be a field of characteristic $p$, and let $M$ be a nonzero natural number with $M \ge 5$ and $p \nmid M$. Write $K_0 :=$ [`ModularCurve.x1FunctionFieldC`](def/ModularCurve_X1.html#L134) $\kappa\,M$ for the intermediate field of the Laurent series field $\kappa((q))$ obtained by adjoining to $\kappa$ the set `intFormRatiosC` $\kappa\,(\Gamma_1(M))$, the $q$-expansion function field of $X_1(M)$ over $\kappa$. Let $w$ be an integral weight-one form of level $M$ over $\kappa$, that is: a modular form of weight $1$ on $\Gamma_1(M)$ together with a power series $P \in \mathbb{Z}[[q]]$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of that form, subject to the condition that the Laurent series $\bar P \in \kappa((q))$ obtained from the reduction of $P$ modulo $p$ is nonzero; its associated function is $w.\mathrm{hasseRootFn} = \bar P^{-1}$. The assertion is that there exists a monoid homomorphism $\varphi$ from the unit group $K_0^\times$ to $\mathbb{Z}$ written multiplicatively, such that for every unit $b$ of $K_0$ whose underlying Laurent series equals $\bar P^{-(p-1)}$, the natural absolute value of the integer $\varphi(b)$ is coprime to $p-1$. No algebraic closedness is assumed of $\kappa$.
--
--   This packages Igusa's simple-zero property of the Hasse invariant $A = E_{p-1} \bmod p$ on $X_1(M)$ in characteristic $p$ into the form needed later: a normalised order function at a supersingular place, restricted to the $q$-expansion function field, whose value on $\bar E_{p-1}/\bar f_1^{\,p-1} = \bar P^{-(p-1)}$ is prime to $p-1$. It feeds the statement that the Hasse root function is a Kummer generator and that the Igusa cover of $X_1(M)$ has relative degree exactly $p-1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_monoidHom_units_x1FunctionFieldC_coprime_of_coe_eq_hasseRootFn_pow
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M) :
    ∃ φ : (↥(ModularCurve.x1FunctionFieldC κ M))ˣ →* Multiplicative ℤ,
      ∀ b : (↥(ModularCurve.x1FunctionFieldC κ M))ˣ,
        ((b : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = w.hasseRootFn ^ (p - 1) →
        (Multiplicative.toAdd (φ b)).natAbs.Coprime (p - 1) := by sorry
