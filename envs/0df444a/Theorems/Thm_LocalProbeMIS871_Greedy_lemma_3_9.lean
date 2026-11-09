-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_lemma_3_9
-- name    : LocalProbeMIS871.Greedy.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:52:52.032615+00:00
-- url     : https://prove2.me/theorems/e635306f-59a2-4d44-9a4a-3c1172623bac
-- title:
--   Lemma 3.9 — An additional inequality for D and X
-- statement:
--   Let $G$ be a finite simple undirected labeled graph, let $v$ be its fixed query root, and use the cached, early-stopping greedy evaluation. Write $R$ for its fresh evaluated vertices, $U=|R|$, $\tau(u)$ for elimination times, $M_s=\sum_{u\in R}\tau(u)^s$, $X=\sum_{u\in R\setminus\{v\}}\tau(u)^s$, $D=\sum_{u\in R\setminus\{v\}}\tau(u)^s\ln(r(u)/\tau(u))$, and $c_s=\ln(s-1)-1$. Unless stated otherwise below, the root has rank $1$ and the other ranks are independent uniforms on $(0,1)$.
--
--   For every real $s>1$, the specific coefficient integrals $u_s,w_s$ of Eq.(30) are integrable and satisfy $u_s,w_s>0$. There is a nonnegative measurable real random variable $L_2$ such that
--
--   $$D\le u_sL_2+u_s(sD-c_sX)+w_sX\quad\text{almost surely},\qquad \mathbb E e^{L_2}\le2.$$
--
--   The coefficients are fixed computed integrals; the statement includes their positivity and finiteness, and imposes no assumption $su_s<1$.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: probability and exponential expectation under the stated independent uniform ranks → the product rankLaw or its forced-root pushforward; exponential expectations use ExpBound; reason: the nonnegative Lebesgue integral and its measurability clause express the same random-variable expectation and cannot default to zero on divergence
--   - encoding: positive finite coefficients given explicitly in Eq.(30) and a nonnegative random variable → coeffU and coeffW with IntegrableOn conclusions, and a globally nonnegative measurable representative whose inequality is almost sure; reason: the integrability assertions prevent default Bochner values; representatives differ only on null inputs
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 20, PDF p. 22, Lemma 3.9, Eq.(27), and Eq.(30) (PDF p.24 / printed p.22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Elimination
import Definitions.Def_LocalProbeMIS871_Greedy_Coefficients

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Lemma 3.9, Eq.(27), printed p.20 / PDF22, with the fixed Eq.(30) coefficients. -/
theorem lemma_3_9 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) (hs : 1 < s) :
    IntegrableOn (uIntegrand s) (Set.Ioo (0 : ℝ) 1) ∧
    IntegrableOn (wIntegrand s) (Set.Ioo (0 : ℝ) 1) ∧
    0 < coeffU s ∧ 0 < coeffW s ∧
    ∃ L₂ : (Fin n → ℝ) → ℝ, Measurable L₂ ∧ (∀ r, 0 ≤ L₂ r) ∧
      (∀ᵐ r ∂forcedLaw v,
        D G v s r ≤ coeffU s * L₂ r + coeffU s * (s * D G v s r - c s * X G v s r) +
          coeffW s * X G v s r) ∧ ExpBound (forcedLaw v) L₂ 2 := by sorry

end LocalProbeMIS871.Greedy
