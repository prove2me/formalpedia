-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
-- name    : ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/7cad61a0-4107-5e22-9198-6c14a969db1f
-- title:
--   The two Igusa charts meet exactly where j, resp. 1/j, is invertible
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$, write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) and $F$ for the full modular function field `modularFunctionFieldFull N`, and let $j \in F$ be the element `jFull N` given by $j$-invariant $q$-expansion. The two charts are the $\mathbb{Z}_{(\ell)}$-subalgebras $A_{\mathrm{fin}} =$ `chartAlg N ℓ {jFull N}` and $A_{\infty} =$ `chartAlg N ℓ {(jFull N)⁻¹}` of $F$, with distinguished elements `jChartFin N ℓ` $= j \in A_{\mathrm{fin}}$ and `jInvChartInf N ℓ` $= j^{-1} \in A_{\infty}$; the scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two morphisms $f_{\mathrm{fin}} \colon \operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\mathrm{fin}}$ and $f_{\infty} \colon \operatorname{Spec} A_{\mathrm{mid}} \to \operatorname{Spec} A_{\infty}$ induced by the inclusions `inclFin`, `inclInf` of the two charts into the overlap algebra, and $\iota_{\mathrm{fin}}, \iota_{\infty}$ are the resulting morphisms from the charts into the pushout, with `chartFinOpen`, `chartInfOpen` their open ranges. The assertion is the conjunction of two equalities of open subsets: the $\iota_{\infty}$-preimage of the open range of $\iota_{\mathrm{fin}}$ equals the basic open $D(j^{-1}) \subseteq \operatorname{Spec} A_{\infty}$, and the $\iota_{\mathrm{fin}}$-preimage of the open range of $\iota_{\infty}$ equals the basic open $D(j) \subseteq \operatorname{Spec} A_{\mathrm{fin}}$.
--
--   This identifies the overlap of the two charts of the Igusa scheme inside the pushout: the $j$-finite chart and the pole chart meet precisely on the locus where $j$, respectively $j^{-1}$, is invertible, so that the pushout is the expected two-chart gluing. It is used in the study of the forgetful morphism of the Deligne–Rapoport model package, in particular for its flatness, finiteness and finite presentation, and for the disjointness of the cuspidal sections from the $j$-finite chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
namespace ModularCurve.IgusaScheme

theorem iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ιInf N ℓ ⁻¹ᵁ chartFinOpen N ℓ = PrimeSpectrum.basicOpen (jInvChartInf N ℓ) ∧
    ιFin N ℓ ⁻¹ᵁ chartInfOpen N ℓ = PrimeSpectrum.basicOpen (jChartFin N ℓ) := by sorry
