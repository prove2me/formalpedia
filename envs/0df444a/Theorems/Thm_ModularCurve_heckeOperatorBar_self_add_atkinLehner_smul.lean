-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul
-- name    : ModularCurve.heckeOperatorBar_self_add_atkinLehner_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/31640a83-5228-51c2-836e-1f771b3bcaca
-- title:
--   Uₚ + wₚ = β^*α_* on J₀(N₀p)
-- statement:
--   Let $N_0$ and $p$ be nonzero natural numbers, let $p$ be prime and suppose $p \nmid N_0$. Let $x$ be an element of `JZero (N₀ * p)`, the group $\mathrm{Pic}^0$ of degree-zero divisor classes (degree-zero divisors modulo principal ones) of the geometric modular function field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb{Q}}$. Three operators on this group occur. First, `heckeOperatorBar (N₀ * p) ⟨p, hp⟩`, the $\mathbb{Z}$-linear endomorphism of `JZero (N₀ * p)` obtained from the Hecke correspondence at $p$ in level $N_0p$ over $\overline{\mathbb{Q}}$. Second, the automorphism `atkinLehnerInvolutionFull N₀ p` of the rational function field `modularFunctionFieldFull (N₀ * p)` — a chosen $\mathbb{Q}$-algebra automorphism satisfying the predicate `IsAtkinLehnerAutFull N₀ p` if one exists, and the identity otherwise — transported by `geomAut` to a $\overline{\mathbb{Q}}$-algebra automorphism of the base change, acting on divisor classes; this acts on $x$ by the scalar action written `•`. Third, the degeneracy maps: `degeneracyPushforwardPair N₀ p 0`, the push-forward $\alpha_*\colon \mathrm{Pic}^0$ of level $N_0p$ $\to \mathrm{Pic}^0$ of level $N_0$ along `heckeAlphaBar`, and `degeneracyPullbackPair N₀ p 1`, the pull-back $\beta^*$ in the opposite direction along `heckeBetaBar` (both defined by the corresponding push-forward, resp. pull-back, homomorphisms when the relevant integrality, finiteness and fundamental-identity inputs hold, and as the zero map otherwise). The assertion is the identity $$U_p\,x + w_p\cdot x = \beta^{*}\bigl(\alpha_{*}x\bigr).$$
--
--   This is the classical Atkin–Lehner relation $U_p + w_p = \beta^{*}\alpha_{*}$ on $J_0(N_0p)$ for $p \nmid N_0$, in the orientation in which $\alpha$ is the degeneracy map forgetting the $p$-level structure; it expresses the failure of $U_p$ to be an involution-twisted projector on the $p$-old part. It is used in the analysis of the Néron model of $J_0(N_0p)$ at $p$ and of the toric part of its reduction, in the Ribet-style level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.heckeOperatorBar_self_add_atkinLehner_smul (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) (x : JZero (N₀ * p)) :
    heckeOperatorBar (N₀ * p) ⟨p, hp⟩ x
        + (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)) • x =
      degeneracyPullbackPair N₀ p 1 (degeneracyPushforwardPair N₀ p 0 x) := by sorry
