-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin
-- name    : ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ccc12a3a-4979-5e48-83e2-e6e02dd74bc1
-- title:
--   Geometric fibres of Igusa's X₀(N₀) as curve models
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$, let $\kappa$ be an algebraically closed field of characteristic $q$, and let $\mathrm{to}\kappa\colon R_q\to\kappa$ be a ring homomorphism from the base ring `DRLevel.R q`. The assertion is the existence of a `CurveModel` $M$ over $\kappa$ for the field $\kappa(\tilde\jmath,\tilde\jmath_{N_0})=$ `modularFunctionFieldC κ N₀`, the intermediate field of $\kappa((q))$ generated over $\kappa$ by `jqModC κ` and `jqNModC κ N₀` — that is, an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$, together with an isomorphism of that field with the function field of $M.C$ over $\kappa$ and a bijection between the closed points of $M.C$ and the places of the field over $\kappa$ matching stalks with valuation rings — and of a morphism $e\colon M.C\to$ `DRLevel.fibre0 toκ`, the fibre product of `DRLevel.toBase0 N₀ q` $\colon X_0(N_0)\to\operatorname{Spec}R_q$ with $\operatorname{Spec}(\mathrm{to}\kappa)$, such that: $e$ is an isomorphism; the open subscheme of $M.C$ obtained by pulling back along $e$ followed by the first projection the image of the finite chart `IgusaScheme.ιFin N₀ q` is nonempty; $e$ followed by the second projection is $M.\mathrm{toBase}$; and, for every $b$ in the chart algebra `IgusaScheme.chartAlgFin N₀ q`, the element $\mathrm{read}\,b$ of $\kappa(\tilde\jmath,\tilde\jmath_{N_0})$ obtained by transporting $b$ through the chart's global-sections identification, pulling it back along $e$ followed by the first projection to the chart preimage, taking its germ in the function field and applying the inverse of $M.\mathrm{ffEquiv}$, satisfies: $\mathrm{read}\,b=$ `jGeomGen κ N₀` if $b=$ `IgusaScheme.jChartFin N₀ q`, and $\mathrm{read}\,b=$ `jNGeomGen κ N₀` if the Laurent series over $\mathbb{Q}$ underlying $b$ equals `qExpand ℚ N₀ jq`, the $q$-expansion $j(q^{N_0})$.
--
--   This is the good-reduction statement for Igusa's two-chart model of $X_0(N_0)$ at a prime $q\nmid N_0$, in the form of a dictionary: every geometric fibre of characteristic $q$ is a smooth proper model of the characteristic-$q$ modular function field, and the two chart generators are read there as the distinguished generators $\tilde\jmath$ and $\tilde\jmath_{N_0}$. It supplies the special-fibre data of the level-$N_0$ Deligne–Rapoport model package used by [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.DRLevel
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    ∃ (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (_ : IsIso e)
      (_ : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
        ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))),
      e ≫ pullback.snd _ _ = M.toBase ∧
      ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)) := by sorry
