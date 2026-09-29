-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self
-- name    : ModularCurve.degeneracyPushforwardPair_one_heckeOperatorBar_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/04c5b6b6-a489-531d-a473-8322996ca253
-- title:
--   Degeneracy relation β_*∘ Uₚ = p α_* on J₀
-- statement:
--   Fix natural numbers $N_0$ and $p$, both nonzero, with $p$ prime, and let $y$ be an element of `JZero (N₀ * p)`, that is, of the degree-zero divisor class group $\mathrm{Pic}^0$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N_0p$ (the quotient of degree-zero divisors by the principal ones). Here `heckeOperatorBar (N₀ * p) ⟨p, hp⟩` is the $\mathbb{Z}$-linear endomorphism of that group obtained from `heckeOperatorAlong` at level $N_0p$ and the prime $p$, i.e. the Hecke correspondence construction `heckePic0Bar` when the inputs `HeckeInputsAlong` are available and the zero map otherwise; and `degeneracyPushforwardPair N₀ p` is the pair of additive maps `JZero (N₀ * p) →+ JZero N₀` given, when `DegeneracyPushforwardInputs N₀ p` holds, by divisor-class pushforward along the two degeneracy embeddings of modular function fields, index $0$ along `heckeAlphaBar` (the inclusion coming from level divisibility $N_0 \mid N_0p$) and index $1$ along `heckeBetaBar` (the map induced by the $q$-expansion twist), and by the zero maps otherwise. The assertion is the identity $\beta_*\big(U_p\,y\big) = p\cdot \alpha_*(y)$, where $\alpha_*$ and $\beta_*$ denote the maps of index $0$ and $1$ respectively and $p\cdot$ is the $\mathbb{Z}$-scalar action on `JZero N₀`. No coprimality between $p$ and $N_0$ is assumed.
--
--   This is one of the two classical relations between the degeneracy maps $X_0(N_0p)\to X_0(N_0)$ and the Hecke operator $U_p$ at level $N_0p$, in the pushforward form $\beta_*\circ U_p = p\,\alpha_*$ on Jacobians. It is used in the analysis of the $p$-adic Tate module of $J_0(N_0 p)$ attached to a newform, in particular for the computations of monodromy spans and Frobenius congruences that underlie level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPushforwardPair_one_heckeOperatorBar_self.lean

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
variable (N₀ p : ℕ) [NeZero N₀] [NeZero p] (hp : p.Prime)

theorem ModularCurve.degeneracyPushforwardPair_one_heckeOperatorBar_self (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 1 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      (p : ℤ) • degeneracyPushforwardPair N₀ p 0 y := by sorry
