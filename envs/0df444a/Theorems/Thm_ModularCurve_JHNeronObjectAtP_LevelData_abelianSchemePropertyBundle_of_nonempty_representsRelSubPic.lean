-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_abelianSchemePropertyBundle_of_nonempty_representsRelSubPic
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.abelianSchemePropertyBundle_of_nonempty_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/072e78d3-3ada-54e9-9838-5501d64b2362
-- title:
--   Representing Pic⁰ makes the level datum an abelian scheme
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^\times$, and hypotheses $p \mid M$ and $p^2 \nmid M$, together with the hypothesis `hj` that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` of the full modular group. Let $\mathfrak{X}$ be a Deligne–Rapoport model package `XHDRModelAtP p M H hpM hj` for the modular curve of level $M$ and character group $H$ over the base ring `R p`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, and let $\Lambda$ be level data `JHNeronObjectAtP.LevelData p M H hpM A`, so in particular $\Lambda$ provides a scheme $\Lambda.X$, a morphism $\Lambda.f$ to the base, a relative group law $\Lambda.L$ for $\Lambda.f$, and point dictionaries at the generic and special fibres. Assume that the designation with underlying scheme $\Lambda.X$, structure morphism $\Lambda.f$ and zero section the identity section of $\Lambda.L$ represents the relative Picard subfunctor cut out by `algEquivZeroCut`, i.e. fibrewise algebraic equivalence to zero, for the level-$\Gamma_N$ integral model `toBase p (ΓN p M H hpM) hj` rigidified along the section obtained by composing $\mathfrak{X}.\varepsilon_{\inf}$ with $\mathfrak{X}.\pi$; representability here means the existence of a rigidified Poincaré bundle lying in the cut, the universal property that every rigidified line bundle in the cut over a base-scheme $T$ is pulled back from it along a unique section over the base, and triviality of the pullback along the zero section. The conclusion is that $\Lambda.f$ satisfies `AbelianSchemePropertyBundle` over `baseRing p`: $\Lambda.f$ is smooth, proper, each fibre of its underlying map over a point of the base is connected, and $\Lambda.f$ admits a relative group law.
--
--   This is the step asserting that the $\mathrm{Pic}^0$ of the smooth level-$\Gamma_N$ integral model at a prime exactly dividing the level is an abelian scheme over the local base, in the packaged form consumed further on. It converts the representability conjunct produced by the Deligne–Rapoport bridge into the abelian-scheme hypothesis used by the torus-part, toric-coordinate and Hecke-stability results for the level-$H$ Néron object at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_abelianSchemePropertyBundle_of_nonempty_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.LevelData.abelianSchemePropertyBundle_of_nonempty_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hrepΛ :
      Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj)))) :
    GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f := by sorry
