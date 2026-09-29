-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compZero_compl_range_compInf
-- name    : ModularCurve.DRModelPackage.isOpenImmersion_restrict_compZero_compl_range_compInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/6819f613-0245-5608-898c-da1ee87c7ab7
-- title:
--   Off the image of i_∞, i₀ is an open immersion
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a term of the structure `DRModelPackage p` — the bundled data and properties attached to the two-chart integral model `DRModel p` (the pushout of the two charts of the modular function field of level $p$ with Igusa parameter $j$) and its structural morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb Z$ — and let $\kappa$ be an algebraically closed field of characteristic $p$. Write $F$ for the geometric fibre, the pullback of `DRModel.toBase p` along $\operatorname{Spec}$ of the structure map $\mathbb Z \to \kappa$. The package supplies two morphisms $\mathfrak X.\mathrm{compInf}\,\kappa$ and $\mathfrak X.\mathrm{compZero}\,\kappa$ into $F$, each a closed immersion by the package fields `compInf_isClosedImmersion` and `compZero_isClosedImmersion`. Since $\mathfrak X.\mathrm{compInf}\,\kappa$ is a closed embedding on points, the image of its underlying map is closed, and its complement is an open subset $W$ of $F$. The assertion is that the open immersion of the open subscheme $(\mathfrak X.\mathrm{compZero}\,\kappa)^{-1}(W)$ into the source of $\mathfrak X.\mathrm{compZero}\,\kappa$, followed by $\mathfrak X.\mathrm{compZero}\,\kappa$ itself, is an open immersion into $F$.
--
--   In the Deligne–Rapoport picture the fibre at $p$ of the model of $X_0(p)$ is a union of two components meeting transversally; this statement says that away from the first component the second one sits inside the geometric fibre as an open subscheme. It is used in the two results identifying the function field and the residue fields at the points of the components of the geometric fibre (`…_of_residueField_compInf` and `…_of_residueField_compZero`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compZero_compl_range_compInf.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.isOpenImmersion_restrict_compZero_compl_range_compInf
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    :
    IsOpenImmersion
      ((𝔛.compZero κ ⁻¹ᵁ
          (⟨(Set.range (𝔛.compInf κ).base)ᶜ,
            (@Scheme.Hom.isClosedEmbedding _ _ (𝔛.compInf κ) (𝔛.compInf_isClosedImmersion κ)).isClosed_range.isOpen_compl⟩ :
            (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).Opens)).ι ≫ 𝔛.compZero κ) := by sorry
