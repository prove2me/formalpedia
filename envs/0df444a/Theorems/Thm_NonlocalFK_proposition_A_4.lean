-- Prove2me | Theorems.Thm_NonlocalFK_proposition_A_4
-- name    : NonlocalFK.proposition_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:03.84573+00:00
-- url     : https://prove2.me/theorems/de5ba92a-f64f-4304-a2b9-83c3d0fd0f86
-- title:
--   Proposition A.4 — the uniform limit solves the nonlocal problem
-- statement:
--   The uniform limit of $(W_i)_{i\ge1}$ on $\bar Q$ is a bounded solution in $C^{1,2}(Q)\cap C(\bar Q\setminus D)$ to the nonlocal problem (1.1)–(1.2).
--
--   This is the existence part of the main theorem.
--
--   Differences from the source:
--   - encoding: bounded smooth domain → open, connected, bounded, with a global $C^\infty$ defining function $\rho$; reason: equivalent for bounded domains; the paper gives no degree of smoothness, read as $C^\infty$
--   - encoding: $f$ uniformly Hölder on $\bar Q$ with exponent $\alpha$ → Hölder for the metric of $\mathbb R\times\mathbb R^d$ with an existential $\alpha\in(0,1]$; reason: with $\alpha$ existential this and the parabolic Hölder class coincide on the bounded set $\bar Q$
--   - reading: $d$-dimensional balls, open or closed not specified → open balls; reason: the two readings agree, since $\varepsilon$ is arbitrary and balls can be slightly enlarged
--   - reading: measurability of $(t,x)\mapsto\nu_{t,x}$ with respect to the weak convergence topology → Borel for the topology of `FiniteMeasure` on $Q$; reason: this is the direct meaning of the phrase
--   - generalization: $|h(s,x)|\le K_h\cdot s$, (2.16) → $|h(s,x)|\le K_h\cdot T$ on $\partial_pQ$; reason: (2.16) implies this bound because $s\le T$, and the proofs use only this bound (p.23)
--   - encoding: the functions $W_i$ of §3 → any sequence with $W_0=0$ on $\bar Q$ and $W_{i+1}$ a bounded solution with data $h+\mathcal BW_i$; reason: Proposition A.1 provides such a sequence and determines it on $\bar Q$
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, Proposition A.4, p.26

import Definitions.Def_NonlocalFK_Realization

open MeasureTheory Set Filter

universe u

namespace NonlocalFK

/-- Proposition A.4 (Dai, Kou, Yang, SSRN 3541591, p.26): the uniform limit of `(Wᵢ)` on `Q̄` is a
bounded solution in `C^{1,2}(Q) ∩ C(Q̄ ∖ D)` to the nonlocal problem (1.1)–(1.2). -/
theorem proposition_A_4 {d : ℕ} (m : Model d) (hS : m.Standing) (h22 : m.Assumption22) {Kh : ℝ}
    (hG : m.Growth Kh) (W : ℕ → ℝ × E d → ℝ) (hW : m.IsIteration W) (L : ℝ × E d → ℝ)
    (hL : TendstoUniformlyOn W L atTop m.Qbar) : m.IsSolution L := by sorry

end NonlocalFK
