-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_observation_2_2
-- name    : InterdepSOS.RSVCG.observation_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:31.601025+00:00
-- url     : https://prove2.me/theorems/0843a076-9585-4147-b151-71e5596b15d1
-- title:
--   Observation 2.2, p. 12 — a separable SOS valuation function is itself SOS
-- statement:
--   Let the bundle valuations $v_{iT}$ be separable SOS with decomposition
--   $$v_{iT}(s_T) = g_{-iT}(s_{-iT}) + h_{iT}(s_{iT}),$$
--   where $g_{-iT}$ and $h_{iT}$ are weakly increasing and $g_{-iT}$ is SOS (Definition 2.16). Then for every agent $i$ and every nonempty bundle $T$, the function $v_{iT} : \mathbb{R}_+^n \to \mathbb{R}$ is SOS: for every coordinate $j$, all $x, \delta \ge 0$ and all profiles $s, s'$ with $s'_l \le s_l$ for $l \ne j$,
--   $$v_{iT}(s_{-j}, x+\delta) - v_{iT}(s_{-j}, x) \le v_{iT}(s'_{-j}, x+\delta) - v_{iT}(s'_{-j}, x).$$
--
--   This is what allows the Key Lemma 3.1 (with $d = 1$) to be applied to separable valuations in the analysis of RS-VCG.
--
--   **Formalization Note** The statement is for nonempty bundles, where the decomposition is assumed; the empty bundle has value $0$ under the standing hypotheses.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 12, Observation 2.2

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting

namespace InterdepSOS.RSVCG

theorem observation_2_2 {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hsep : IsSeparableSOS v g h) (i : Fin n) (T : Bundle m) (hT : T.Nonempty) :
    IsSOS (v i T) := by sorry

end InterdepSOS.RSVCG
