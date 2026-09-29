-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self
-- name    : ModularCurve.degeneracyPushforwardPair_zero_heckeOperatorBar_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/b3e27c64-b444-533c-9eab-d21e4bc65ff2
-- title:
--   Degeneracy relation α_*Uₚ=Tₚα_*-β_* at a prime p∤ N₀
-- statement:
--   Let $N_0$ and $p$ be nonzero natural numbers with $p$ prime and $p \nmid N_0$, and let $y$ be an element of `JZero (N₀ * p)`, the group $\mathrm{Pic}^0$ of degree-zero divisors modulo principal divisors for the field `modularFunctionFieldBar (N₀ * p)`, that is the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N_0p$ inside Laurent series. The two maps `degeneracyPushforwardPair N₀ p 0` and `degeneracyPushforwardPair N₀ p 1` are additive maps `JZero (N₀ * p) →+ JZero N₀` given, when the integrality, finiteness and norm-formula package `DegeneracyPushforwardInputs N₀ p` holds (as it does for prime $p$), by divisor-class pushforward along the two degeneracy embeddings of function fields `heckeAlphaBar` (the inclusion coming from $N_0 \mid N_0p$) and `heckeBetaBar` (the embedding twisting $q$-expansions by $q \mapsto q^{p}$), and by $0$ otherwise; `heckeOperatorBar M ⟨p, hp⟩` is the $\mathbb{Z}$-linear endomorphism of `JZero M` given by the Hecke operator at $p$ in level $M$. The assertion is the identity $$\alpha_*\bigl(T_p^{(N_0p)} y\bigr) = T_p^{(N_0)}\bigl(\alpha_* y\bigr) - \beta_*(y),$$ where $\alpha_*$, $\beta_*$ are the two pushforwards above and $T_p^{(M)}$ denotes `heckeOperatorBar M ⟨p, hp⟩`.
--
--   This is the classical relation between the two degeneracy coverings $X_0(N_0p) \to X_0(N_0)$ and the Hecke operators at $p$, in Albanese (pushforward) form: the operator at level $N_0p$, classically $U_p$, is carried by $\alpha_*$ to $T_p\alpha_* - \beta_*$. It governs the action of the $p$-th Hecke operator on the $p$-old part of $J_0(N_0p)$ and is used in the analysis of newform eigenplanes in the Tate module and of monodromy at $p$, as required in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.lean

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.degeneracyPushforwardPair_zero_heckeOperatorBar_self (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 0 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      heckeOperatorBar N₀ ⟨p, hp⟩ (degeneracyPushforwardPair N₀ p 0 y) -
        degeneracyPushforwardPair N₀ p 1 y := by sorry
