-- Prove2me | Theorems.Thm_IoTFusion_KnownQuality_remark_1
-- name    : IoTFusion.KnownQuality.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:24.831251+00:00
-- url     : https://prove2.me/theorems/3d248fcf-ea53-403a-bb88-988060fb6ed2
-- title:
--   Remark 1, p. 20 — sensor i targets j infinitely often along a sample path iff j is a long-run contact of i
-- statement:
--   Let $q_i > 0$ for every sensor and $v_{ij0}, w_{ij0} > 0$ for every pair. Fix a sample path $S_\infty = (s_0, s_1, \dots)$, a sensor $i$ and a sensor $j \neq i$. Then
--
--   $$j \in T_i(S_\infty) \iff j^*_{it} = j \text{ for infinitely many periods } t,$$
--
--   where $T_i(S_\infty)$ is the set of long-run contacts of $i$ (Definition 2) and $j^*_{it}$ is $i$'s target in period $t$.
--
--   The remark turns the analytic condition $\psi_{ijt}(s_{t-1}) \to \infty$ into a combinatorial one about the target sequence, which is how the proof of Proposition 4 uses long-run contacts.
--
--   **Formalization Note** Lean step $k$ is the paper's period $k+1$; "infinitely often" is `∃ᶠ k in atTop, target P i s k = j`. The positivity hypotheses are the paper's standing assumptions (noise variance $1/q_i^2$; initial beliefs with finite positive precisions, p. 11); they make the stickiness factor and the initial familiarity positive.
-- source:
--   Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 20, Remark 1

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model

namespace IoTFusion.KnownQuality

/-- **Remark 1 (Infinitely-Often Communication)**, Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 20.

Along any state path `s`, sensor `i` targets sensor `j ≠ i` infinitely often if and only if `j`
is a long-run contact of `i` (Definition 2, (20)).

**Formalization Note.** Sensors are `Fin n`; Lean step `k` is the paper's period `k + 1`.
"Infinitely often" is `∃ᶠ k in atTop, target P i s k = j`. The hypotheses `hq`, `hv`, `hw` are the
paper's standing assumptions `q_i > 0` (noise variance `1/q_i^2`, (2)) and `v_{ij0}, w_{ij0} > 0`
(p. 11); they make the stickiness factor and the initial familiarity positive. `j ≠ i` is
required because `i` never targets itself. -/
theorem remark_1 {n : ℕ} (P : Instance n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j) (s : ℕ → ℝ) (i j : Fin n) (hj : j ≠ i) :
    j ∈ longRunContacts P i s ↔ ∃ᶠ k in Filter.atTop, target P i s k = j := by sorry

end IoTFusion.KnownQuality
