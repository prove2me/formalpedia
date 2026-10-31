-- Prove2me | Theorems.Thm_Ironclad_relPerf_one_gt_one
-- name    : Ironclad.relPerf_one_gt_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:44.916567+00:00
-- url     : https://prove2.me/theorems/7445c920-058b-488b-882f-44234ddf75a6
-- title:
--   Appendix .2.6, p.33 — $\mathcal R>1$ at $\theta=1$
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $q_h=(1-q)p_h$, $q_H=qp_h$. With $\alpha$ given by (4) at $\theta=1$,
--
--   $$
--   \mathcal R\big|_{\theta=1}=\frac{(1-q_H)^\Delta\big[q_h^2(1-p_h)^{2\Delta}+q_hq_H(1-q_H)^\Delta(1-p_h)^\Delta+p_hq_H(1-q_H)^\Delta\big]}{p_h^2(1-p_h)^{2\Delta}}>1.
--   $$
--
--   With the monotonicity in $\theta$ this gives Theorem 3.2. The paper's argument drops a term, applies the weighted power-mean inequality with weights $q_h/p_h$, $q_H/p_h$ and exponent $\Delta$, and checks $\frac{q_h}{p_h}(1-q_H)+\frac{q_H}{p_h}\frac{1-q_H}{1-p_h}=\frac{1-p_h+q_hq_H}{1-p_h}>1$.
--
--   Differences from the source:
--   - reading: "Let $\theta=1$, and thus $\mathcal R>\dots>\dots$", whose chain ends in "$\mathcal R>1$" → $\mathcal R$ at $\theta=1$, with $\alpha$ given by (4), exceeds $1$; reason: the displayed bound is that value, and the step from $\theta\ge1$ to $\theta=1$ is the monotonicity of `Ironclad.relPerf_strictMonoOn`
--   - reading: no parameter range in App. .2.6 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2, whose proof this is
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.6, proof of Theorem 3.2, p.33 ("Let θ = 1 … we conclude the proof")

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

namespace Ironclad

/-- `R > 1` at `θ = 1`, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, Appendix .2.6, p.33: with
`α` given by (4) at `θ = 1`,
`R = (1 − q_H)^Δ[q_h²(1 − p_h)^{2Δ} + q_h q_H(1 − q_H)^Δ(1 − p_h)^Δ + p_h q_H(1 − q_H)^Δ]/(p_h²(1 − p_h)^{2Δ}) > 1`.

**Formalization Note** The standing parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of
Theorem 3.2. -/
theorem relPerf_one_gt_one (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    1 < relPerf ph q Δ 1 (alphaClosed ph q Δ 1) := by sorry

end Ironclad
