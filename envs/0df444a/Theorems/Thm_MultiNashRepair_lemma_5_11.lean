-- Prove2me | Theorems.Thm_MultiNashRepair_lemma_5_11
-- name    : MultiNashRepair.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:30:53.844204+00:00
-- url     : https://prove2.me/theorems/083837d1-7443-4eb7-afb2-01b6a1716032
-- title:
--   Lemma 5.11 — uniform control down to zero memory: $|K_u(H)-K_{f_0}(H)|\le32u$
-- statement:
--   For $f_0\in[7/12,3/5]$, $0<u\le1/16$ and $0\le H\le L_0$,
--   $$|K_u(H)-K_{f_0}(H)|\le32u\qquad(5.48),$$
--   where $K_u$ is the finite repair coefficient (5.45) and $K_u(0)=G_0$ is its continuous extension at $H=0$.
--
--   With $u\le d/100$ and the choice (5.1) of $f_0$ this gives $K_u(H)>\sigma+6d$ on $[0,L_0]$ (5.50), the strict reserve behind the progress of both branches.
--
--   Differences from the source:
--   - encoding: $K_u(0)=G_0$ denotes its continuous extension → $K_u$ defined with $K_u(0)=G_0$, plus the clause that $K_u$ is continuous at $0$ within $[0,\infty)$; reason: the paper asserts that $G_0$ is the continuous extension
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Lemma 5.11, (5.48), p.37

import Mathlib
import Definitions.Def_MultiNashRepair_ScalarCertificate
import Definitions.Def_MultiNashRepair_Knobs

namespace MultiNashRepair

/-- **Lemma 5.11 (Uniform Control Down to Zero Memory)** (Tang, Ding, Fang, arXiv:2611.06076,
Lemma 5.11, (5.48), p.37).

For `f0 ∈ [7/12, 3/5]`, `0 < u ≤ 1/16` and `0 ≤ H ≤ L0`, `|K_u(H) − K_{f0}(H)| ≤ 32u`, where
`K_u(0) = G0` is the continuous extension of (5.45) at `H = 0`. -/
theorem lemma_5_11 (f0 u : ℝ) (hf1 : 7 / 12 ≤ f0) (hf2 : f0 ≤ 3 / 5) (hu0 : 0 < u)
    (hu1 : u ≤ 1 / 16) :
    let k : Knobs := ⟨f0, u⟩
    k.Ku 0 = k.G0 ∧ ContinuousWithinAt k.Ku (Set.Ici 0) 0 ∧
      ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 → |k.Ku H - Kf f0 H| ≤ 32 * u := by sorry

end MultiNashRepair
