-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq
-- name    : ModularCurve.exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/ae25dae0-0275-56c7-bc28-63ece29219c3
-- title:
--   Two spellings of the q-expansion field of X₁(M)
-- statement:
--   Let $k$ be a field and let $M$ be a natural number, nonzero. Two intermediate fields of the Laurent series field $k((q))$ over $k$ are compared. The first is `x1FunctionFieldC k M`, by definition `qExpFunctionFieldC k (Gamma1 M)`, the subfield of $k((q))$ generated over $k$ by the set `intFormRatiosC` for $\Gamma_1(M)$, namely all quotients $\mathrm{intSeriesC}\,k\,p_f/\mathrm{intSeriesC}\,k\,p_g$ where, for some weight $k_0 \in \mathbb{Z}$, $f$ and $g$ are modular forms for the image of $\Gamma_1(M)$ in $\mathrm{GL}(2,\mathbb{R})$ with integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ (as recorded by `IsIntegralQExp`) and the series attached to $p_g$ over $k$ is nonzero. The second is the same construction `qExpFunctionFieldC k` applied to the subgroup [`CohCarrier.GammaH M ⊥`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, obtained by pulling the trivial subgroup $\bot \le (\mathbb{Z}/M)^\times$ back along the homomorphism `gamma0Units` $: \Gamma_0(M) \to (\mathbb{Z}/M)^\times$, $\gamma \mapsto d(\gamma) \bmod M$, and pushing the result forward along the inclusion $\Gamma_0(M) \le \mathrm{SL}(2,\mathbb{Z})$. The conclusion asserts the existence of a $k$-algebra isomorphism $e$ from the first field to the second such that for every $x$ in the first field, the Laurent series underlying $e(x)$ equals the Laurent series underlying $x$.
--
--   This is a bookkeeping bridge between the two names under which the $q$-expansion function field of $X_1(M)$ over $k$ occurs, the one indexed by $\Gamma_1(M)$ and the one indexed by $\Gamma_H(M)$ with $H$ trivial; the equality of the two congruence subgroups is a proposition rather than a definitional identity, so the transfer is packaged as an explicit isomorphism that is the identity on $q$-expansions. It is used in the analysis of the integral model of the map $X_1 \to X_0$ and its inertia subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq
    (k : Type*) [Field k] (M : ℕ) [NeZero M] :
    ∃ e : ↥(x1FunctionFieldC k M) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥)),
      ∀ x : ↥(x1FunctionFieldC k M),
        ((e x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥))) : LaurentSeries k) = (x : LaurentSeries k) := by sorry
