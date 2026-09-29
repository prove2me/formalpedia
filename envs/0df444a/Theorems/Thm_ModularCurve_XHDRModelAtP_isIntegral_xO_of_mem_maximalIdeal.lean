-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal
-- name    : ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9aa9757d-116d-5631-8f50-c6ae389cf8ce
-- title:
--   Integrality of the X_H(M) model over a discrete valuation ring
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and divisibility hypotheses $p \mid M$, $p^2 \nmid M$ (so $p \parallel M$), together with $M/p \neq 0$ and the assumption that every unit $u \in (\mathbb{Z}/M)^\times$ whose image under `ZMod.unitsMap` along $(M/p) \mid M$ is trivial already lies in $H$. Assume $j$, in its $q$-expansion form `jqModC ℚ`, lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for $\mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, i.e. a model datum for the curve `X p (ΓM M H) hj` over `Spec (R p)` packaging properness, flatness, integrality, local finite presentation and normality of the structure morphism `toBase`, together with the corresponding data at level `ΓN`, a curve model over $\overline{\mathbb{Q}}$ identified with the geometric fibre, its Galois compatibility and $q$-expansion pinning, and smoothness and geometric integrality of the generic fibre. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $O$ be a discrete valuation ring (a commutative domain) with a ring homomorphism $\rho_O : R\,p \to O$ such that the image of $p$ in $O$ is non-zero and lies in the maximal ideal of $O$. Then the fibre product `XO (ΓM M H) hj ρO`, the pullback of `toBase p (ΓM M H) hj` along $\operatorname{Spec} \rho_O$, is an integral scheme.
--
--   This is the statement that the Deligne–Rapoport style integral model of $X_H(M)$ at a prime exactly dividing the level remains integral after base change to an arbitrary, possibly ramified, discrete valuation ring in which $p$ is a non-zero non-unit. It is used in the study of sections and stalks of that model, for instance in the lemmas comparing $q$-expansion embeddings with stalk readings at points of the base-changed curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isIntegral_xO_of_mem_maximalIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isIntegral_xO_of_mem_maximalIdeal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : R p →+* O) (hp0 : ((p : ℕ) : O) ≠ 0) (hp : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) :
    IsIntegral (XO (ΓM M H) hj ρO) := by sorry
