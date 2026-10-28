-- Prove2me | Theorems.Thm_OTSensitivity_Consist_eq_80
-- name    : OTSensitivity.Consist.eq_80
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:23.244727+00:00
-- url     : https://prove2.me/theorems/964bf7ee-83bd-497c-be12-406f38a76f3c
-- title:
--   (80)–(81), p. 39 — for finite $\mathsf X$, $\xi^K(Y,X)=\sum_h\mu(\{x^h\})K(\nu,\nu_{x^h})$
-- statement:
--   Let $\mathsf X=\{x^1,\dots,x^H\}$ be a finite set with the discrete topology and $\sigma$-algebra $2^{\mathsf X}$, let $\mathsf Y$ be a Polish space, and let $k$ be a cost satisfying the standing assumption of §3.1 (continuous, $k(y,y')=0\iff y=y'$). Let $\pi$ be the joint law of $(X,Y)$ on $\mathsf X\times\mathsf Y$, with marginals $\mu$ and $\nu$. For each atom with $\mu(\{x^h\})>0$ let $\nu_{x^h}(B)=\mu(\{x^h\})^{-1}\pi(\{x^h\}\times B)$. Then, for every version $(\nu_x)$ of the conditional distribution of $Y$ given $X$,
--   $$\xi^K(Y,X)=\sum_{h:\ \mu(\{x^h\})>0}\mu(\{x^h\})\,K(\nu,\nu_{x^h}).$$
--   Applied to the laws $\pi^N$ this is (81); applied to $\pi$ it is (80).
--
--   This identity reduces the sensitivity measure of a finite-valued input to finitely many optimal transport costs between the marginal and the cell-conditional laws; it is the first step of the proof of Theorem 21 (1).
--
--   **Formalization Note** The statement is made on $\Omega=\mathsf X\times\mathsf Y$ with $\mathbb P=\pi$ and $X$, $Y$ the coordinate projections, since $\xi^K$ depends on $(X,Y)$ only through $\pi$. The paper assumes w.l.o.g. that every atom has positive mass; here the sum runs over the atoms of positive mass, so atoms of mass zero are allowed. Values are in $[0,+\infty]$; $K$ is `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 1, (80)–(81), p. 39

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- (80)–(81), p. 39. For finite `𝒳` and a probability law `π` of `(X, Y)` on `𝒳 × 𝒴`,
`ξ^K(Y, X) = Σ_h μ({x^h}) K(ν, ν_{x^h})`, the sum running over the atoms of positive mass, with
`ν_{x^h}(B) = μ({x^h})⁻¹ π({x^h} × B)`; this holds for every version of the conditional
distribution. -/
theorem eq_80 {𝒳 𝒴 : Type*}
    [Fintype 𝒳] [TopologicalSpace 𝒳] [DiscreteTopology 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (π : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure π] (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib π Prod.fst Prod.snd ‹MeasurableSpace 𝒳› κ) :
    xi k π Prod.fst Prod.snd κ =
      ∑ x ∈ Finset.univ.filter (fun x => π.fst {x} ≠ 0),
        π.fst {x} * RWPI.SqrtLasso.transportCost k π.snd (cellLaw π {x}) := by sorry

end OTSensitivity.Consist
