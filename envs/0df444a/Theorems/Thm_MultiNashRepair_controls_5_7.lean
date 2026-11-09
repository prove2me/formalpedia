-- Prove2me | Theorems.Thm_MultiNashRepair_controls_5_7
-- name    : MultiNashRepair.controls_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:30:40.552452+00:00
-- url     : https://prove2.me/theorems/405d6f3b-cdfb-4042-885a-9093e38ffcdc
-- title:
--   (5.7)–(5.8) — the control bounds $0<R_0<1$, $1<Q<2$, $0<a_u<1$, $L_0<f_0$, $QL_0<c$ and the threshold bounds
-- statement:
--   Let $f_0\in[7/12,3/5]$ and $0<u\le1/16$, and let $c,t,\rho,\beta,\nu,R_0,G_0,Q,a_u,L_0$ be the controls (5.3)–(5.6). Then
--   $$0<R_0<1,\qquad 1<Q<2,\qquad 0<a_u<1,\qquad L_0<f_0,\qquad QL_0<c\qquad(5.7),$$
--   and for every $0\le H\le L_0$
--   $$S_u'(H)\ge1-R_0(Q-1)>0,\qquad S_u(H)\le1+L_0+R_0<\frac{13}{5}\qquad(5.8).$$
--
--   These bounds give the legal reverse allocation of Lemma 5.5 and the finite-step progress of Proposition 4.5.
--
--   Differences from the source:
--   - generalization: the rational controls of §5.1 ($u=\tfrac12\min\{1/144,d/100\}$, rational $f_0$) → every real $f_0\in[7/12,3/5]$ and $0<u\le1/16$; reason: this is the range of the paper's own verification on p.16 ("For u ≤ 1/16 and f ∈ [7/12, 3/5]"); it contains the paper's controls
--   - encoding: $S_u'(H)$ → `deriv k.Su H`; reason: $S_u$ is differentiable on $H\ge0$
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §5.1, (5.7)–(5.8) and their verification, p.16

import Mathlib
import Definitions.Def_MultiNashRepair_Knobs

namespace MultiNashRepair

/-- **The control bounds (5.7) and (5.8)** (Tang, Ding, Fang, arXiv:2611.06076, §5.1, p.16).

For every `f0 ∈ [7/12, 3/5]` and `0 < u ≤ 1/16` (the range of the paper's verification on p.16),
the controls of (5.3)–(5.6) satisfy (5.7): `0 < R0 < 1`, `1 < Q < 2`, `0 < a_u < 1`, `L0 < f0`,
`Q L0 < c`; and (5.8): on `0 ≤ H ≤ L0`,
`S_u'(H) ≥ 1 − R0(Q − 1) > 0` and `S_u(H) ≤ 1 + L0 + R0 < 13/5`. -/
theorem controls_5_7 (f0 u : ℝ) (hf1 : 7 / 12 ≤ f0) (hf2 : f0 ≤ 3 / 5) (hu0 : 0 < u)
    (hu1 : u ≤ 1 / 16) :
    let k : Knobs := ⟨f0, u⟩
    (0 < k.R0 ∧ k.R0 < 1 ∧ 1 < k.Q ∧ k.Q < 2 ∧ 0 < k.au ∧ k.au < 1 ∧ k.L0 < f0 ∧
        k.Q * k.L0 < k.c) ∧
      ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 →
        0 < 1 - k.R0 * (k.Q - 1) ∧ 1 - k.R0 * (k.Q - 1) ≤ deriv k.Su H ∧
          k.Su H ≤ 1 + k.L0 + k.R0 ∧ 1 + k.L0 + k.R0 < 13 / 5 := by sorry

end MultiNashRepair
