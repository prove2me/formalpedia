-- Prove2me | Theorems.Thm_OceanPlastic_proposition_1
-- name    : OceanPlastic.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:50:31.014369+00:00
-- url     : https://prove2.me/theorems/5e798b28-3149-4bc0-9a3f-6f2cd2a01ca9
-- title:
--   Proposition 1 — the Benchmark equilibrium: $V^B=Mp_m/(2k)$, $\Pi^B_C=\Pi^B_P=Mp_m^2/(4k)$
-- statement:
--   In the Benchmark Case, for every unit payment $h$ a collector's unique optimal volume, the unique maximizer of $hq-kq^2/2$ over $q\in\mathbb R$, is $q=h/k$, so that $M(h/k)=q_t(h)$. The processor's unique optimal price, the unique maximizer of $(p_m-h)q_t(h)$ over $h\in\mathbb R$, is $h=p_m/2$. At that price the recycled volume, the collectors' total income and the processor's profit are
--   $$V^B=\frac{Mp_m}{2k},\qquad \Pi^B_C=\Pi^B_P=\frac{Mp_m^2}{4k}.$$
--
--   This identifies the closed forms used as the baseline of the firm's problem with the equilibrium of the two-stage benchmark game.
--
--   Differences from the source:
--   - reading: "each collector picks h/k"; "we solve for the equilibrium acquisition price" (p. 8) → unique maximizers over ℝ (`IsMaxOn` … `Set.univ` ↔ the printed value); reason: the paper's "max_q" and "max_h" carry no constraint and the objectives are strictly concave
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
--   - reading: collectors' total income → gross payment (price received) × (volume); reason: the only reading consistent with Π^B_C = Mp_m²/(4k), eq. (3) and Π^{OS}_C = kq_t²/M (p. 14); net utility would be half of it
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, Proposition 1, p.8

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark

namespace OceanPlastic

open Params

/-- **Proposition 1: the Benchmark equilibrium.** Baron–Romero–Zhang–Zhou, *Innovative Business
Models in Ocean-Bound Plastic Recycling*, MSOM, doi:10.1287/msom.2022.0643, Proposition 1, p. 8.

Each collector's unique optimal volume at price `h` is `h / k`, so the total volume is
`M (h / k) = q_t(h)`; the processor's unique optimal price is `h = p_m / 2`; and at that price the
volume, the collectors' total income and the processor's profit are `V^B = M p_m / (2k)` and
`Π^B_C = Π^B_P = M p_m² / (4k)`.

**Formalization Note** "Optimal" is `IsMaxOn` over all of `ℝ`, as printed ("max_q", "max_h").
Collectors' total income is the gross payment `h q_t(h)`. -/
theorem proposition_1 (P : Params) :
    (∀ h q : ℝ, IsMaxOn (P.collectorUtility h) Set.univ q ↔ q = h / P.k) ∧
    (∀ h : ℝ, P.qt h = P.M * (h / P.k)) ∧
    (∀ h : ℝ, IsMaxOn P.processorObjB Set.univ h ↔ h = P.pm / 2) ∧
    P.qt (P.pm / 2) = P.VB ∧
    P.pm / 2 * P.qt (P.pm / 2) = P.PiBC ∧
    P.processorObjB (P.pm / 2) = P.PiBP ∧
    P.VB = P.M * P.pm / (2 * P.k) ∧
    P.PiBC = P.M * P.pm ^ 2 / (4 * P.k) ∧
    P.PiBP = P.M * P.pm ^ 2 / (4 * P.k) := by sorry

end OceanPlastic
