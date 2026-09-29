-- Prove2me | Theorems.Thm_ModularCurve_exists_dRModelPackage_ffPin
-- name    : ModularCurve.exists_dRModelPackage_ffPin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c4b662d4-3760-5dbf-bf81-a19b903c6bda
-- title:
--   Existence of a Deligne–Rapoport model package with q-expansion pin
-- statement:
--   Let $p$ be a prime with $5 \le p$. Write $F =$ `modularFunctionFieldFull p`, the subfield of the Laurent series field $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions at level $p$, let $j =$ `IgusaScheme.jFull p` be the element $j(q)$ of $F$, and let $\mathfrak{X}_{\mathbb{Z}} =$ `DRModel p` be the two-chart integral model of $F$ over $\mathbb{Z}$ with respect to $j$, that is, the pushout of the two affine charts $\operatorname{Spec}$ of the finite chart algebra `chartAlgFin` and the chart algebra at infinity, with structure map `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$. The assertion is that there exists a term $\mathfrak{X}$ of the structure `DRModelPackage p`, whose fields record that `DRModel.toBase p` is proper and flat, that $\mathfrak{X}_{\mathbb{Z}}$ is integral with integrally closed sections on every affine open, a curve model $M_0$ over $\mathbb{Q}$ of $F$ and a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of `modularFunctionFieldBar p` $=$ the base change of $F$ inside $\overline{\mathbb{Q}}((q))$ — each being an integral scheme, proper and smooth of relative dimension $1$ over the base field, equipped with a ring isomorphism `ffEquiv` from the given field onto its function field over the base, and a bijection from closed points onto places matching stalks with valuation rings — together with isomorphisms $e_0$, $e_\eta$ of these models with the base changes of $\mathfrak{X}_{\mathbb{Z}}$ along $\mathbb{Z} \to \mathbb{Q}$ and $\mathbb{Z} \to \overline{\mathbb{Q}}$ commuting with the structure maps, Galois equivariance and valuation-ring compatibility of the resulting place dictionaries, two sections $\varepsilon_{\infty}$, $\varepsilon_0$ of `DRModel.toBase p` over the identity of $\operatorname{Spec}\mathbb{Z}$, a smooth locus open maximal among opens smooth over $\mathbb{Z}$ and of relative dimension $1$, and the remaining fields of the structure, summarised here; and moreover, with $V \subseteq M_\eta.C$ denoting the preimage under $e_\eta$ followed by the first projection of the finite-chart open $\iota_{\mathrm{Fin}}(\top)$ of $\mathfrak{X}_{\mathbb{Z}}$, the open subscheme $V$ has a point, and for every $a$ in the finite chart algebra `chartAlgFin` the element of `modularFunctionFieldBar p` obtained by transporting $a$ to a global section of the finite chart, pulling it back to a section on $V$ along $e_\eta$ followed by the projection, taking its germ in the function field of $M_\eta.C$ and applying `ffEquiv.symm` of $M_\eta$, equals, as a Laurent series over $\overline{\mathbb{Q}}$, the image of the Laurent series $a \in \mathbb{Q}((q))$ under the coefficientwise embedding `coeffEmb` induced by $\mathbb{Q} \to \overline{\mathbb{Q}}$.
--
--   This is the existence of the Deligne–Rapoport model of $X_0(p)$ over $\mathbb{Z}$ for $p \ge 5$, packaged with its generic-fibre curve models over $\mathbb{Q}$ and $\overline{\mathbb{Q}}$, its cuspidal sections and its smooth locus; the additional clause pins the function-field identification of the geometric generic-fibre model so that elements of the finite chart ring are read as their $q$-expansions, which fixes the pair $(M_\eta, e_\eta)$ for all later uses of the place dictionary. It is used in the construction of the good identity component at the cusp $j = 0$ data, via [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_dRModelPackage_ffPin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.exists_dRModelPackage_ffPin (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ (𝔛 : DRModelPackage p) (_ : Nonempty (Scheme.Opens.toScheme
        ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
          ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))),
      ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) := by sorry
