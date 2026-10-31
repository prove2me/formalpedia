-- Prove2me | Theorems.Thm_KallMayerSLP_RecourseBounds_remark_2_3
-- name    : KallMayerSLP.RecourseBounds.remark_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:43.998003+00:00
-- url     : https://prove2.me/theorems/fcb7b64b-2847-4613-afd1-cbb75c7f58af
-- title:
--   Remark 2.3 — for independent components $\mathbb Q$ is the product E–M distribution
-- statement:
--   Let $\operatorname{supp}\mathbb P_\xi\subset\Xi=\times_{i=1}^r[\alpha_i,\beta_i]$ with $\alpha_i<\beta_i$, $\mu=\mathbb E_\xi[\xi]$, and let the components of $\xi$ be stochastically independent. Then the generalized E–M distribution (2.30) is the product E–M distribution of (2.19)–(2.20): for every vertex $v^\nu$,
--   $$
--   \mathbb Q(v^\nu)=\prod_{i\in I_\nu}\frac{\beta_i-\mu_i}{\beta_i-\alpha_i}\cdot\prod_{i\in J_\nu}\frac{\mu_i-\alpha_i}{\beta_i-\alpha_i}.
--   $$
--
--   So Lemma 2.7 contains Lemma 2.6 as the independent special case.
--
--   **Formalization Note** The product weight is the platform's `emVertexWeight α β μ v`.
--
--   Differences from the source:
--   - encoding: random vector ξ with distribution IP_ξ, supp IP_ξ ⊂ Ξ = ×ᵢ[αᵢ, βᵢ] → probability measure P on Fin r → ℝ with P(Ξᶜ) = 0, Ξ = Set.Icc α β; reason: every quantity depends only on the law of ξ; Ξ is closed, so supp IP_ξ ⊂ Ξ is P(Ξᶜ) = 0; ℝ^r is Fin r → ℝ (0-based index)
--   - encoding: components of ξ stochastically independent → iIndepFun of the coordinate maps under P; reason: the definition of independence of the components
--   - encoding: the two-point laws (2.19) divide by βᵢ − αᵢ → hypothesis αᵢ < βᵢ for every i; reason: excludes exactly the boxes where (2.19) is undefined
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Remark 2.3, p.216 (PDF 225)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky
import Definitions.Def_KallMayerSLP_RecourseBounds_genEMWeight

open MeasureTheory

namespace KallMayerSLP.RecourseBounds

/-- **Chapter 3, Remark 2.3 — for independent components `Q` is the product E–M distribution.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Remark 2.3, printed p.216 (PDF 225):
"Observe that for stochastically independent components of `ξ`, due to (2.30) we get for the
generalized E–M distribution `Q(v^ν) = ∏_{i∈I_ν} (βᵢ − μᵢ)/(βᵢ − αᵢ) · ∏_{i∈J_ν} (μᵢ − αᵢ)/(βᵢ − αᵢ)`,
such that in this case `Q` coincides with the E–M distribution `IP_η` for the independent case as
derived in (2.19) and (2.20)."

**Formalization Note.** `IP_ξ` is a probability measure `P` on `Fin r → ℝ` with `P(Ξᶜ) = 0`,
independence is `iIndepFun` of the coordinate maps, `μᵢ = ∫ ξᵢ dP`. The product weight is the
platform's `NumStochOpt.Bounds.emVertexWeight α β μ v`; `αᵢ < βᵢ` is the nondegeneracy the formula
divides by. -/
theorem remark_2_3 {r : ℕ} (P : Measure (Fin r → ℝ)) [IsProbabilityMeasure P]
    (α β : Fin r → ℝ) (hαβ : ∀ i, α i < β i) (hsupp : P (Set.Icc α β)ᶜ = 0)
    (hind : ProbabilityTheory.iIndepFun (fun i (ξ : Fin r → ℝ) => ξ i) P) :
    ∀ v : Fin r → Bool, genEMWeight P α β v =
      NumStochOpt.Bounds.emVertexWeight α β (fun i => ∫ ξ, ξ i ∂P) v := by sorry

end KallMayerSLP.RecourseBounds
