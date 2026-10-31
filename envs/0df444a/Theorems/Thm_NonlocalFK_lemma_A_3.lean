-- Prove2me | Theorems.Thm_NonlocalFK_lemma_A_3
-- name    : NonlocalFK.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:44:53.040053+00:00
-- url     : https://prove2.me/theorems/37a777e6-47c6-45fe-afe9-0ea480bffd17
-- title:
--   Lemma A.3 — $(W_i)$ converges uniformly on $\bar Q$
-- statement:
--   The sequence of functions $(W_i)$ of §3 converges uniformly on $\bar Q$.
--
--   Differences from the source:
--   - encoding: bounded smooth domain → open, connected, bounded, with a global $C^\infty$ defining function $\rho$; reason: equivalent for bounded domains; the paper gives no degree of smoothness, read as $C^\infty$
--   - encoding: $f$ uniformly Hölder on $\bar Q$ with exponent $\alpha$ → Hölder for the metric of $\mathbb R\times\mathbb R^d$ with an existential $\alpha\in(0,1]$; reason: with $\alpha$ existential this and the parabolic Hölder class coincide on the bounded set $\bar Q$
--   - reading: $d$-dimensional balls, open or closed not specified → open balls; reason: the two readings agree, since $\varepsilon$ is arbitrary and balls can be slightly enlarged
--   - reading: measurability of $(t,x)\mapsto\nu_{t,x}$ with respect to the weak convergence topology → Borel for the topology of `FiniteMeasure` on $Q$; reason: this is the direct meaning of the phrase
--   - generalization: $|h(s,x)|\le K_h\cdot s$, (2.16) → $|h(s,x)|\le K_h\cdot T$ on $\partial_pQ$; reason: (2.16) implies this bound because $s\le T$, and the proofs use only this bound (p.23)
--   - encoding: the functions $W_i$ of §3 → any sequence with $W_0=0$ on $\bar Q$ and $W_{i+1}$ a bounded solution with data $h+\mathcal BW_i$; reason: Proposition A.1 provides such a sequence and determines it on $\bar Q$
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, Lemma A.3, p.26

import Definitions.Def_NonlocalFK_Realization

open MeasureTheory Set Filter

universe u

namespace NonlocalFK

/-- Lemma A.3 (Dai, Kou, Yang, SSRN 3541591, p.26): the sequence of functions `(Wᵢ)` converges
uniformly in `Q̄`. -/
theorem lemma_A_3 {d : ℕ} (m : Model d) (hS : m.Standing) (h22 : m.Assumption22) {Kh : ℝ}
    (hG : m.Growth Kh) (W : ℕ → ℝ × E d → ℝ) (hW : m.IsIteration W) :
    ∃ L : ℝ × E d → ℝ, TendstoUniformlyOn W L atTop m.Qbar := by sorry

end NonlocalFK
