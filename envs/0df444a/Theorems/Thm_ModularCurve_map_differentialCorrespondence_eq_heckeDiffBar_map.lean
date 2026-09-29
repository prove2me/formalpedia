-- Prove2me | Theorems.Thm_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map
-- name    : ModularCurve.map_differentialCorrespondence_eq_heckeDiffBar_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/b9fec2a4-3563-5986-bc16-42f2eabb6144
-- title:
--   Base change to ℚ̄ of the Hecke correspondence on differentials
-- statement:
--   Fix $p\ge 1$ and a prime $q$, and write $F_N=$ `modularFunctionFieldFull` $N$ for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions` $N$, and $\overline F_N=$ `modularFunctionFieldBar` $N$ for its base change `laurentBaseChange` to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$. Let $\varphi_\alpha,\varphi_\beta\colon F_p\to F_{pq}$ be ring homomorphisms, regarded as $\mathbb{Q}$-algebra maps, and assume: for every $f\in F_p$, the degeneracy inclusion `heckeAlphaBar` $\overline{\mathbb{Q}}\,p\,q$ (induced by $F_p\subseteq F_{pq}$) sends the image of $1\otimes f$ under `baseChangeEquiv` to the image of $1\otimes\varphi_\alpha f$, and likewise `heckeBetaBar` $\overline{\mathbb{Q}}\,p\,q$ (the map induced by `heckeBetaBarRingHom`, acting on Laurent expansions by the substitution $q\mapsto q^{q}$) sends the image of $1\otimes f$ to that of $1\otimes\varphi_\beta f$; moreover $F_{pq}$ is finite as a module over $F_p$ via $\varphi_\beta$. Let $\kappa\colon\Omega_{F_p/\mathbb{Q}}\to\Omega_{\overline F_p/\overline{\mathbb{Q}}}$ be the $\mathbb{Q}$-linear map obtained by pulling back differentials along $f\mapsto 1\otimes f$ followed by `baseChangeEquiv`, and then applying `KaehlerDifferential.map` $\mathbb{Q}\,\overline{\mathbb{Q}}$ for $\overline F_p$. Then for every $\omega\in\Omega_{F_p/\mathbb{Q}}$,
--   $$\kappa\bigl(\mathrm{tr}_{\varphi_\beta}(\varphi_\alpha^{*}\omega)\bigr)=\bigl(\mathtt{heckeDiffBar}\;p\;q\bigr)\bigl(\kappa(\omega)\bigr),$$
--   where the left-hand side is `Differential.correspondence` $\varphi_\beta\,\varphi_\alpha$ (pull-back along $\varphi_\alpha$ followed by the trace along $\varphi_\beta$, the latter taken to be $0$ unless `SeparableAlong` holds) and `heckeDiffBar` $p\,q$ is the $\overline{\mathbb{Q}}$-linear endomorphism `heckeDiffAlong` $\overline{\mathbb{Q}}\,p\,q$ of $\Omega_{\overline F_p/\overline{\mathbb{Q}}}$.
--
--   This is the compatibility of the cotangent action of the Hecke correspondence at $q$ on the modular curve of level $p$ with extension of the field of constants from $\mathbb{Q}$ to $\overline{\mathbb{Q}}$: pull-back along the first degeneracy map and trace along the second may be computed over $\mathbb{Q}$ and then base changed. It is used by [`ModularCurve.kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar`](thm.html#ModularCurve.kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar), where the Hecke action on differentials over $\overline{\mathbb{Q}}$ is transported back to the function field over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential AlgebraicCurve ModularCurve
namespace ModularCurve
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem map_differentialCorrespondence_eq_heckeDiffBar_map
    (p : ℕ) [NeZero p] (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (hα : ∀ f : ↥(modularFunctionFieldFull p),
      heckeAlphaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f))
    (hβ : ∀ f : ↥(modularFunctionFieldFull p),
      heckeBetaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f))
    (hfin : FiniteAlong ℚ φβ.toRatAlgHom)
    (ω : Ω[↥(modularFunctionFieldFull p)⁄ℚ]) :
    ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
      (Differential.pullbackAlong
        (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p))))
        (Differential.correspondence φβ.toRatAlgHom φα.toRatAlgHom ω)) =
    heckeDiffBar p q
      (((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
            ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
        (Differential.pullbackAlong
          (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))) ω)) := by sorry
