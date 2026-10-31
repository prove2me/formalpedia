-- Prove2me | Theorems.Thm_Ironclad_alphaPiMu_eq_alphaClosed
-- name    : Ironclad.alphaPiMu_eq_alphaClosed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:33.450137+00:00
-- url     : https://prove2.me/theorems/53f36ccb-9fcd-4b2b-9321-80e91ab4560c
-- title:
--   Lemma 3.1, second sentence — the $(\pi,P,\mu)$ expression of $\alpha$ equals the exact expression (4)
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $\theta\in\mathbb R$, $q_h=(1-q)p_h$, $q_H=qp_h$. With $\pi$ the stationary distribution of App. .2.2, $P$ the matrix (3), $\mu_i=\sum_jP_{ij}l_{ij}$ and $A=\sum_{i=0}^2\pi_i\mu_i$,
--
--   $$
--   \frac{\pi_0P_{00}\mathbb P(\sigma_2)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]A}\Big(1-\frac{\pi_2P_{20}}{\sum_{i=0}^2\pi_iP_{i0}}\Big)+\theta\,\frac{\pi_0P_{00}\mathbb P(\sigma_4)+\pi_1P_{10}\mathbb P(\sigma_4)}{[\mathbb P(\sigma_2)+\mathbb P(\sigma_4)]A}
--   =\frac1{p_h}\Big[(1-q_H)^\Delta\big(q_h^2(1-p_h)^{2\Delta}+q_Hq_h(1-p_h)^\Delta(1-q_H)^\Delta+\theta p_hq_H(1-q_H)^\Delta\big)\Big].
--   $$
--
--   This is the algebraic half of Lemma 3.1: it turns the renewal-theoretic value of $\alpha$ into the explicit formula (4) on which Theorem 3.2 is computed.
--
--   Differences from the source:
--   - generalization: $\theta>1$ (p.5) → any real $\theta$; reason: an identity of functions of $\theta$; specializes to $\theta>1$
--   - reading: no parameter range in Lemma 3.1 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2; at $q=0$, $P_{20}$ and $\mathbb E|\sigma_3|$ divide by zero
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Lemma 3.1 (first display and Eq. (4)), p.13

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

namespace Ironclad

/-- Lemma 3.1, second sentence, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.13: the
expression of `α` through the stationary distribution `π`, the transition matrix (3) and the
sojourn times `μ_i = Σ_j P_ij l_ij` equals the exact expression (4).

**Formalization Note** The identity holds for every real `θ`; the paper has `θ > 1`. The standing
parameter range `0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem alphaPiMu_eq_alphaClosed (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) (θ : ℝ) :
    alphaPiMu ph q Δ θ = alphaClosed ph q Δ θ := by sorry

end Ironclad
