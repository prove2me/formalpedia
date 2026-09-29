-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
-- name    : ModularCurve.JHPlaceSpecialization.reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/41883989-813e-5adb-a777-6e2b01896880
-- title:
--   Second reading at a φ-fixed place equals δ(φ(r₁))
-- statement:
--   Fix a prime $p$ and a natural number $M\neq 0$ with $p\mid M$ and $M/p\neq 0$, a subgroup $H\le(\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Let $FM=\overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ and $FMp=\overline{\mathbb{Q}}\cdot F(\Gamma_{H'}(M/p))$, where $H'$ is the image of $H$ under $(\mathbb{Z}/M)^\times\to(\mathbb{Z}/(M/p))^\times$, and let $\alpha,\beta\colon FMp\to FM$ be integral $\overline{\mathbb{Q}}$-algebra maps. Write $\mathrm{Fb}$ for the $q$-expansion function field over $\kappa$ attached to $\Gamma_N(p,M,H)$ and $\varphi=$ `qExpFrobeniusPlaceModL` for the induced self-map of places of $\mathrm{Fb}$ over $\kappa$, and let $\delta$ be an arbitrary self-map of that set of places. Let $\mathrm{Psp}$ be a `JHPlaceSpecialization`, so in particular it provides a surjective map $\mathrm{sp}$ from places of $FMp$ over $\overline{\mathbb{Q}}$ to places of $\mathrm{Fb}$ over $\kappa$ together with a map on degree-zero divisor classes, compatibility of $\mathrm{sp}$ with orders of vanishing of matching $q$-expansions, invariance under inertia at $A$ and $\varphi$-equivariance under Frobenius elements at $A$. Put $r_1=\mathrm{sp}(W|_\alpha)$ and $r_2=\delta(\mathrm{sp}(W|_\beta))$ for a place $W$ of $FM$ over $\overline{\mathbb{Q}}$, restriction being along $\alpha$, resp.\ $\beta$. Assume the type dichotomy: for every place $W'$ of $FM$ one has $\mathrm{sp}(W'|_\alpha)=\varphi(\delta(\mathrm{sp}(W'|_\beta)))$ or $\delta(\varphi(\mathrm{sp}(W'|_\alpha)))=\delta(\mathrm{sp}(W'|_\beta))$. If moreover $\varphi(\delta(\varphi(r_1)))=r_1$, then $r_2=\delta(\varphi(r_1))$.
--
--   At a place where the first reading is fixed by $\varphi\circ\delta\circ\varphi$, the type dichotomy collapses to its second alternative, so the second reading is determined by the first; this is the place-level form of the two-component picture of the modular curve in characteristic $p$ and of the Eichler–Shimura congruence. It is used by the common-unit arguments for prolongation data, which need both readings of a single place simultaneously.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.reduceSnd_eq_apply_qExpFrobeniusPlaceModL_reduceFst_of_fixed_of_typeDichotomy
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W)) :
    Psp.reduceSnd β hβ δ W =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W)) := by sorry
