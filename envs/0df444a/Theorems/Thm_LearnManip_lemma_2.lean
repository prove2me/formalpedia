-- Prove2me | Theorems.Thm_LearnManip_lemma_2
-- name    : LearnManip.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:55.700877+00:00
-- url     : https://prove2.me/theorems/8d63babb-662d-406e-a59b-f54fc4d31a3b
-- title:
--   Lemma 2, p.12 (corrected: $\gamma>0$, attainment when $H$ is $G^*$-integrable) — the variational formula, its identity and uniqueness
-- statement:
--   Let $F$ be a probability measure, $\gamma>0$, $H$ measurable with $e^{H/\gamma}$ $F$-integrable, and let $G^*$ have $F$-density $e^{H/\gamma}/E_F[e^{H/\gamma}]$. For every probability measure $G\ll F$ of finite relative entropy with $H$ $G$-integrable, $D(G\|G^*)$ is finite and
--   $$E_G[H]-\gamma D(G\|F)=\gamma\log E_F\bigl[e^{H/\gamma}\bigr]-\gamma D(G\|G^*).$$
--   Hence the left side is at most $\gamma\log E_F[e^{H/\gamma}]$, with equality iff $G=G^*$. This bound is the least upper bound over all such $G$, which is the formula (11). If moreover $H$ is $G^*$-integrable, then $G^*$ has finite relative entropy and attains it.
--
--   This is the step that removes the distortion from the dynamic program.
--
--   Differences from the source:
--   - correction: γ a non-negative constant → γ > 0; reason: at γ = 0 the expression H/γ is undefined
--   - correction: the supremum is attained at G* → attained when H is G*-integrable; reason: take F such that Y = H/γ ≥ 0 has density ∝ e^{−y}/(1+y²): then e^Y is F-integrable, E_{G*}[H] = D(G*‖F) = ∞, and no G attains the supremum
--   - reading: G ∈ P(R), the distributions with e^{H/γ} integrable → G ≪ F with H G-integrable and D(G‖F) finite; reason: these are the G for which the objective of (11) is defined and not −∞
--   - generalization: F, G distributions on ℝ → F, G probability measures on any measurable space; reason: the proof uses nothing about ℝ; taking Ω = ℝ gives the source's case
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 2, p.12; proof, p.ec7 (PDF 46)

import Mathlib

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Lemma 2, p.12, with the identity of its proof, p.ec7 (PDF 46), of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04), **corrected**: for `γ > 0`, `H` measurable and `e^{H/γ}` `F`-integrable, with
`G* = F.tilted (H/γ)` the law (12), every probability `G ≪ F` of finite relative entropy with `H`
`G`-integrable satisfies `E_G[H] − γ D(G‖F) = γ log E_F[e^{H/γ}] − γ D(G‖G*)`, so it is at most
`γ log E_F[e^{H/γ}]`, with equality iff `G = G*`. That bound is the least upper bound (11). If moreover
`H` is `G*`-integrable, `G*` attains it.

**Formalization Note.** The printed lemma is false: `γ = 0` makes `H/γ` undefined, and if `H` is not
`G*`-integrable the supremum need not be attained. Its `P(ℝ)` is read as: `G ≪ F`, `H` `G`-integrable,
finite relative entropy, the distributions for which the objective of (11) is defined and not `−∞`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (F : Measure Ω) [IsProbabilityMeasure F] {γ : ℝ}
    (hγ : 0 < γ) {H : Ω → ℝ} (hH : Measurable H)
    (hexp : Integrable (fun ω => Real.exp (H ω / γ)) F) :
    (∀ (G : Measure Ω) [IsProbabilityMeasure G], G ≪ F → Integrable H G → klDiv G F ≠ ∞ →
      klDiv G (F.tilted fun ω => H ω / γ) ≠ ∞ ∧
      ∫ ω, H ω ∂G - γ * (klDiv G F).toReal =
        γ * Real.log (∫ ω, Real.exp (H ω / γ) ∂F)
          - γ * (klDiv G (F.tilted fun ω => H ω / γ)).toReal ∧
      ∫ ω, H ω ∂G - γ * (klDiv G F).toReal ≤ γ * Real.log (∫ ω, Real.exp (H ω / γ) ∂F) ∧
      (∫ ω, H ω ∂G - γ * (klDiv G F).toReal = γ * Real.log (∫ ω, Real.exp (H ω / γ) ∂F) ↔
        G = F.tilted fun ω => H ω / γ)) ∧
    IsLUB {x : ℝ | ∃ G : Measure Ω, IsProbabilityMeasure G ∧ G ≪ F ∧ Integrable H G ∧
        klDiv G F ≠ ∞ ∧ x = ∫ ω, H ω ∂G - γ * (klDiv G F).toReal}
      (γ * Real.log (∫ ω, Real.exp (H ω / γ) ∂F)) ∧
    (Integrable H (F.tilted fun ω => H ω / γ) →
      klDiv (F.tilted fun ω => H ω / γ) F ≠ ∞ ∧
      ∫ ω, H ω ∂(F.tilted fun ω => H ω / γ)
          - γ * (klDiv (F.tilted fun ω => H ω / γ) F).toReal =
        γ * Real.log (∫ ω, Real.exp (H ω / γ) ∂F)) := by sorry

end LearnManip
