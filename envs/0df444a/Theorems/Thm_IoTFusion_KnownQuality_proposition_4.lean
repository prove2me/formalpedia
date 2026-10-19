-- Prove2me | Theorems.Thm_IoTFusion_KnownQuality_proposition_4
-- name    : IoTFusion.KnownQuality.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:22.439748+00:00
-- url     : https://prove2.me/theorems/75d8547e-3d80-4c70-8935-b41440edb185
-- title:
--   Proposition 4, p. 21 — with asymmetric qualities, every sensor has exactly one long-run contact along every sample path
-- statement:
--   Consider $n \ge 2$ sensors with qualities $q_i > 0$ and initial familiarities $v_{ij0}, w_{ij0} > 0$, each sensor targeting in every period the other sensor of least signal variance (ties to the lower index), with familiarities evolving by the familiarity dynamics (12), (14). Suppose the qualities are **asymmetric**: $q_j \neq q_{j'}$ for all $j \neq j'$ (Definition 3). Then for every sample path $S_\infty = (s_0, s_1, s_2, \dots)$ of real states,
--
--   $$|T_i(S_\infty)| = 1 \qquad \text{for all } i \in N,$$
--
--   where $T_i(S_\infty) = \{ j \neq i : \lim_{t\to\infty} \psi_{ijt}(s_{t-1}) = \infty \}$ is the set of long-run contacts of $i$ (Definition 2).
--
--   Each sensor therefore eventually settles on exactly one partner; which partner depends on the path and need not be the highest-quality sensor. This is the paper's main structural result on the long-run communication network.
--
--   **Formalization Note** The hypotheses $n \ge 2$ and $q_i > 0$ are implicit in the paper (for $n = 1$, $T_i = \emptyset$; the noise variance is $1/q_i^2$); $v_{ij0}, w_{ij0}$ are finite and positive as on p. 11. Asymmetry is `Function.Injective P.q`. A sample path is an arbitrary real sequence; no probabilistic assumption enters. $|T_i|$ is `Set.ncard`. The paper's printed proof shows $|T_i| \le 1$; the existence half is the separate item `long_run_contacts_nonempty`.
-- source:
--   Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 21, Proposition 4 (with Definition 3, p. 21)

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model

namespace IoTFusion.KnownQuality

/-- **Proposition 4 (Unique Long Run Contact)**, Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 21.

If the sensor qualities are asymmetric (Definition 3: `q_j ≠ q_{j'}` whenever `j ≠ j'`), then
along every state path `s`, every sensor `i` has exactly one long-run contact:
`|T_i(S∞)| = 1` (Definition 2, (20)).

**Formalization Note.** Sensors are `Fin n` with `2 ≤ n` (implicit in the paper: for `n = 1`,
`T_i = ∅`). `hq : q_i > 0` (noise variance `1/q_i^2`, (2)) and `hv`, `hw`: `v_{ij0}, w_{ij0} > 0`
finite (p. 11) are the paper's standing assumptions. Asymmetric qualities are
`Function.Injective P.q`. A sample path is an arbitrary real sequence `s` (`s k = s_k`); no
probabilistic assumption is needed. `|T_i|` is `Set.ncard`. The familiarity `ψ` is the paper's
familiarity dynamics (12) + (14) and the target is the least-index variance minimizer (11) with
footnote 11, as in `Definitions.Def_IoTFusion_KnownQuality_Model`. -/
theorem proposition_4 {n : ℕ} (P : Instance n) (hn : 2 ≤ n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j)
    (hasym : Function.Injective P.q) (s : ℕ → ℝ) :
    ∀ i : Fin n, (longRunContacts P i s).ncard = 1 := by sorry

end IoTFusion.KnownQuality
