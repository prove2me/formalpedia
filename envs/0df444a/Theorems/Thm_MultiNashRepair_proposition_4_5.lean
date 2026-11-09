-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_5
-- name    : MultiNashRepair.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:19.543871+00:00
-- url     : https://prove2.me/theorems/31c9b42f-5eef-42d4-8376-379b23c025e7
-- title:
--   Proposition 4.5 — uniform progress: $H\Delta\widehat\Phi\ge\eta d/2$ (descent) and $\ge3d(1-c)$ (repair)
-- statement:
--   Fix admissible controls for $\sigma$ and $m\ge m_0$, and a nonterminal scalar state $(\varsigma,H)$ with $\varsigma<\sigma$ and $0<H\le L_0$; put $\mu=S_u(H)-\varsigma-d$ and
--   $$\widehat\Phi_u(\varsigma,H)=\frac{\varsigma-G_0+2d}{H}+(1-a_u)\log\frac{H}{f_0}+a_u\log(1+QH).$$
--   1. **Successful LP step.** For every $Z\in[0,1]$ and $1-\eta Z\le P\le1$, if $\varsigma^+\ge P[(1+\eta Z)\varsigma+\eta\mu]$ and $H^+=PH$, then $H\,\Delta\widehat\Phi\ge\eta d/2>0$.
--   2. **Repair step.** For every $0\le E\le120u/m$, if $\varsigma^+\ge c\varsigma+D-E$ with $D=\beta(G_0+QH)$ and $H^+=c(H+t)$, then $H\,\Delta\widehat\Phi\ge3d(1-c)>0$.
--
--   Here $\Delta\widehat\Phi=\widehat\Phi_u(\varsigma^+,H^+)-\widehat\Phi_u(\varsigma,H)$.
--
--   Differences from the source:
--   - generalization: descent and repair steps of Algorithm 1 at nonterminal states with $H>0$ → every scalar transition satisfying the bounds of Lemma 5.1 and Proposition 4.3; reason: every IDRH step satisfies them (Lemma 5.1, Proposition 4.3); contains the paper's steps
--   - encoding: a state of a run (with $H\le L_0$ by (5.53)) → the hypothesis $H\le L_0$; reason: the invariant of Lemma 5.12 that the proof uses
--   - generalization: the scaled satisfaction $\varsigma=m(1-\mathrm{Reg}(x))\ge0$ of a state → any real $\varsigma<\sigma$; reason: both bounds of the proof on p.39 are sign-free in $\varsigma$; contains the paper's states
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), Proposition 4.5, p.14; proof p.39; potential (4.11), p.14, and (5.51), p.38

import Mathlib
import Definitions.Def_MultiNashRepair_Controls

namespace MultiNashRepair

/-- **Proposition 4.5 (Uniform Progress in Both Branches)** (Tang, Ding, Fang,
arXiv:2611.06076, Proposition 4.5, p.14; proof p.39; potential (4.11)/(5.51)).

Fix admissible controls, `m ≥ m0`, and a nonterminal scalar state `(ς, H)` with `ς < σ` and
`0 < H ≤ L0`; put `µ = S_u(H) − ς − d` and `Φ̂_u(ς, H) = (ς − G0 + 2d)/H + (1 − a_u) log(H/f0)
+ a_u log(1 + QH)`. A successful LP step — any `Z ∈ [0,1]`, `1 − ηZ ≤ P ≤ 1`,
`ς⁺ ≥ P[(1 + ηZ)ς + ηµ]`, `H⁺ = PH` (Lemma 5.1) — satisfies `H ΔΦ̂ ≥ ηd/2 > 0`; a repair step —
any `0 ≤ E ≤ 120u/m`, `ς⁺ ≥ cς + D − E`, `H⁺ = c(H + t)` (Proposition 4.3) — satisfies
`H ΔΦ̂ ≥ 3d(1 − c) > 0`.

**Formalization Note.** Stated for the scalar step relations of Lemma 5.1 and Proposition 4.3,
which every IDRH step satisfies at a reachable state (Lemma 5.12 gives `H ≤ L0`). -/
theorem proposition_4_5 {σ : ℚ} (ctrl : Controls σ) {m : ℕ} (hm : ctrl.m0 ≤ m) (ς H : ℝ)
    (hH0 : 0 < H) (hHL : H ≤ ctrl.knobs.L0) (hς : ς < σ) :
    let k := ctrl.knobs
    let d : ℝ := ctrl.d
    let η : ℝ := ctrl.η
    let mu := ctrl.mu ς H
    (∀ Z P ς' H' : ℝ, 0 ≤ Z → Z ≤ 1 → 1 - η * Z ≤ P → P ≤ 1 →
      P * ((1 + η * Z) * ς + η * mu) ≤ ς' → H' = P * H →
      η * d / 2 ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    (∀ E ς' H' : ℝ, 0 ≤ E → E ≤ 120 * (ctrl.u : ℝ) / m →
      k.c * ς + k.Dsh H - E ≤ ς' → H' = k.c * (H + k.t) →
      3 * d * (1 - k.c) ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    0 < η * d / 2 ∧ 0 < 3 * d * (1 - k.c) := by sorry

end MultiNashRepair
