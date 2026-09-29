-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
-- name    : ModularCurve.DRModelPackage.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/f2fbf027-55de-593c-b7ee-389d46c98cb1
-- title:
--   Germ of p regular and stalk dimension ≥ 2 at a crossing
-- statement:
--   Let $p$ be a prime with $5 \le p$ and let $\mathfrak{X}$ be a term of `DRModelPackage p`, the structure bundling the two-chart integral model `DRModel p` of the modular function field `modularFunctionFieldFull p` over $\mathbb{Z}$ together with properness, flatness and integrality of `DRModel.toBase p`, integral closedness of its sections on affine opens, curve models over $\mathbb{Q}$ and over $\overline{\mathbb{Q}}$ with their Galois compatibilities, two sections $\varepsilon_\infty, \varepsilon_0$ over $\operatorname{Spec}\mathbb{Z}$, a maximal smooth locus, and the further data naming the two components of the fibre at $p$. Let $O$ be a discrete valuation domain whose maximal ideal is $(p)$, let $\kappa$ be an algebraically closed field of characteristic $p$ and $\mathrm{to}\kappa : O \to \kappa$ a ring homomorphism, and write $X_O :=$ `baseChangeO p O` for the pullback of `DRModel.toBase p` along $\operatorname{Spec}(\mathbb{Z} \to O)$. Let $n$ be a point of the fibre product of $\mathfrak{X}.\mathrm{compInf}\,\kappa$ and $\mathfrak{X}.\mathrm{compZero}\,\kappa$, and let $x_n := \mathfrak{X}.\mathrm{crossingPt}\,O\,\kappa\,\mathrm{to}\kappa\,n$ be its image in $X_O$ under $\mathrm{pullback.fst}$ followed by $\mathfrak{X}.\mathrm{compInf}\,\kappa$ followed by `DRModel.baseChangeMap toκ`. Assume the two points $\mathfrak{X}.\xi_{\inf}$ and $\mathfrak{X}.\xi_{\mathrm{zero}}$ (over $O$, $\kappa$, $\mathrm{to}\kappa$) both specialise to $x_n$. Then the germ at $x_n$ of the global section of $X_O$ obtained by pulling back $p \in O$ along the structure morphism $X_O \to \operatorname{Spec} O$ is a non-zero-divisor in the stalk $\mathcal{O}_{X_O, x_n}$, and $\operatorname{ringKrullDim} \mathcal{O}_{X_O, x_n} \ge 2$ in $\mathbb{N}_\infty \cup \{\bot\}$.
--
--   This records the two local facts about the Deligne–Rapoport model base-changed to $O$ at a crossing point of its fibre at $p$: the uniformiser of $O$ is a regular element of the local ring there, and that local ring has dimension at least two. It is used in the construction of oriented crossing charts ([`ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart`](thm.html#ModularCurve.DRModelPackage.forall_exists_orientedCrossingChart)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRModelPackage

theorem ModularCurve.DRModelPackage.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)))
    (hinf : 𝔛.ξinf O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) (hzero : 𝔛.ξzero O κ toκ ⤳ 𝔛.crossingPt O κ toκ n) :
    baseGerm O (𝔛.crossingPt O κ toκ n) ((p : ℕ) : O) ∈
      nonZeroDivisors ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) ∧
    (2 : WithBot ℕ∞) ≤ ringKrullDim ((baseChangeO p O).presheaf.stalk (𝔛.crossingPt O κ toκ n)) := by sorry
