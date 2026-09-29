-- Prove2me | Theorems.Thm_KServer_level_step_full
-- name    : KServer.level_step_full
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T21:38:03.359549+00:00
-- url     : https://prove2.me/theorems/5ac041d3-4354-4b8a-b84b-81992ecdabca
-- title:
--   The full BCR level step with explicit parameters
-- statement:
--   One complete level step of the Bansal–Cohen–Ravi style lower-bound recursion, with all parameter dependencies explicit. Given a taut metric space with marked points $s \\ne t$ and a level-$w$ chunk system between them with size ceiling $c$, expected total $T$, escape price $p$, exactly $M$ chunks, a trivial initial history, and total-variance at most $V$, the step (i) regroups the chunks on the mass grid of mesh $2\\delta$ into exactly $M'$ windows, (ii) pads empty chunks, and (iii) races four copies of the resulting system on the theta gluing of the level step of the space, using $\\kappa$ coin steps of tie-break scale $\\varepsilon$ and window floor $c_{Lo}'$. The output is a level-$(w+1)$ chunk system between the new marked points (whose distance is three times the old one) with ceiling $2\\delta + c$, exactly $3M' + \\kappa$ chunks, trivial initial history, expected total at least $3T + G/2$ minus explicit lower-order losses, and variance at most roughly $5$ times the regrouped variance plus lower-order terms. Here $G$ is the anti-concentration gain: the expected imbalance of the coin race, bounded below via the martingale anti-concentration inequality applied to the padded imbalance martingale, with the expected off-window step count controlled by the retirement argument in terms of the mass defect $M'(2\\delta+c) - T$.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound: the induction step of Lemma 6

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_fold
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_geo

namespace KServer

open Race ThetaChain

theorem level_step_full {X : Type*} [MetricSpace X] {s t : X}
    (hst : s ≠ t)
    (htaut : ∀ x : X, dist s x + dist x t = dist s t)
    {c T p V : ℝ} {M : ℕ}
    (C : ChunkSystemB X s t 0 c T p M) (hm : C.m = M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    {δ ε cLo' p' p'' V1 G T3 V3 : ℝ} {M' κ : ℕ}
    (hδ : 0 < δ) (hc0 : 0 ≤ c) (hc2δ : c ≤ 2 * δ)
    (hM'0 : 0 < M') (hM'M : M' ≤ M) (hκM' : κ ≤ M')
    (hTmax : (M : ℝ) * c ≤ 2 * δ * (M' : ℝ))
    (hε : 0 < ε) (hεLo : ε ≤ cLo') (hLo2δ : cLo' < 2 * δ + c)
    (hp0 : 0 ≤ p) (hpp' : p + (2 * δ + c) ≤ p')
    (hp'D : p' ≤ dist s t) (hp'p'' : p' ≤ p'')
    (hV0 : 0 ≤ V)
    (hV1 : 5 / 4 * V + 20 * ((2 * δ + c) * ((M : ℝ) * c)) ≤ V1)
    (hG : G ≤ Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (2 * δ + c + ε) ^ 2) ^ 2
          + 3 * (2 * δ + c + ε) ^ 2 * ((κ : ℝ) * (2 * δ + c + ε) ^ 2)))
      - (κ : ℝ) * ε
      - (2 * δ + c + ε + cLo')
        * (4 * ((M' : ℝ) * (2 * δ + c) - T) / (2 * δ + c - cLo')))
    (hT3 : T3 ≤ 3 * T + G / 2 - 2 * (2 * δ + c) - (κ : ℝ) * ε / 2
      - 2 * Real.sqrt V1)
    (hV3 : V1 + (2 * V1 + 2 * (((κ : ℝ) + 1) * (2 * δ + c))
          * Real.sqrt (2 * V1)
        + (((κ : ℝ) + 1) * (2 * δ + c)) ^ 2)
      + (2 * V1 + 2 * (2 * δ + c) ^ 2) ≤ V3) :
    letI := stepMetric s t hst
    ∃ C' : ChunkSystemB (Step s t hst) (stepS s t hst) (stepT s t hst)
        0 (2 * δ + c) T3 p'' (3 * M' + κ),
      C'.m = 3 * M' + κ ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V3) := by
  sorry

end KServer
