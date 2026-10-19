-- Prove2me | Theorems.Thm_KanCombine_Optimal_y_moments
-- name    : KanCombine.Optimal.y_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:22.884025+00:00
-- url     : https://prove2.me/theorems/bb7739f1-bf39-49f7-b098-92827c716bf6
-- title:
--   Proof of Lemma 1, p. 32 — first and second moments of the auxiliary variables y₁, y₂ of (13)–(14)
-- statement:
--   Let $N > 3$ and $h > N + 3$, and let $z_2 \sim \mathcal N(\sqrt h\,\psi, 1)$, $u_0 \sim \chi^2_{N-2}$, $v_2 \sim \chi^2_{h-N+1}$, $w_1 \sim \chi^2_{h-N+3}$, $w_2 \sim \chi^2_{h-N+2}$, $s_1 \sim \chi^2_{N-4}$, $s_2 \sim \chi^2_{N-3}$ and $x_{11}, x_{21}, a, b, c \sim \mathcal N(0,1)$ be mutually independent random variables (the auxiliary family of Proposition 1, with $\psi^2 \ge 0$). Define, as in eqs. (13)–(14),
--   $$y_1 = \frac{x_{11}}{\sqrt{w_1}} + \frac{b\,x_{21}}{\sqrt{w_1 w_2}} + \frac{a\,x_{21}}{\sqrt{v_2 w_2}}, \qquad y_2 = \frac{c}{\sqrt{w_1}} + \frac{b\sqrt{s_2}}{\sqrt{w_1 w_2}} + \frac{a\sqrt{s_2}}{\sqrt{v_2 w_2}}.$$
--   Then $y_1$, $y_2$, $y_1^2$ and $y_2^2$ are integrable, and
--   $$E[y_1] = E[y_2] = 0, \qquad E[y_1^2] = \frac{1}{h-N-1}, \qquad E[y_2^2] = \frac{h+N-7}{(h-N-1)(h-N+1)}.$$
--
--   These are the facts the proof of Lemma 1 uses to pass from the stochastic representation (A4)–(A8) of the out-of-sample moments to their expectations (A9)–(A13).
--
--   **Formalization Note** The auxiliary family and $y_1$, $y_2$ are the published definitions of `RiskEU.OOSUVar.KanRepresentation` (Lassance et al.'s restatement of this paper's Proposition 1, with this paper's $h$ in the role of their $T$). The hypothesis $N > 3$ is Proposition 1's: for $N = 2, 3$ footnote 8 sets $c$, $s_2$ (and more) to zero, which makes $y_2 = 0$ and the stated second moment false.
-- source:
--   Kan, Wang & Zhou, Optimal portfolio choice with estimation risk: No risk-free asset case, submitted manuscript (version of November 2020; SSRN 2819254, TSpace), p. 32 (PDF 35), proof of Lemma 1, 'using the fact that E[y1] = E[y2] = 0, E[y²₁] = 1/(h−N−1), and E[y²₂] = (h+N−7)/[(h−N−1)(h−N+1)]'; variables from Proposition 1 and eqs. (13)–(14), p. 7 (PDF 10)

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace KanCombine.Optimal

open MeasureTheory ProbabilityTheory RiskEU.OOSUVar

/-- Proof of Lemma 1, p. 32: for N > 3 and h > N + 3, with the independent auxiliary variables of
Proposition 1 (p. 7) and y₁, y₂ of (13)–(14), E[y₁] = E[y₂] = 0, E[y₁²] = 1/(h − N − 1) and
E[y₂²] = (h + N − 7)/((h − N − 1)(h − N + 1)). -/
theorem y_moments {N h : ℕ} (hN : 3 < N) (hh : N + 3 < h) (psi2 : ℝ) (hpsi : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N h psi2 Q X) :
    Integrable (fun ω => KanVar.y1 N (fun i => X i ω)) Q ∧
    Integrable (fun ω => KanVar.y2 N (fun i => X i ω)) Q ∧
    Integrable (fun ω => KanVar.y1 N (fun i => X i ω) ^ 2) Q ∧
    Integrable (fun ω => KanVar.y2 N (fun i => X i ω) ^ 2) Q ∧
    ∫ ω, KanVar.y1 N (fun i => X i ω) ∂Q = 0 ∧
    ∫ ω, KanVar.y2 N (fun i => X i ω) ∂Q = 0 ∧
    ∫ ω, KanVar.y1 N (fun i => X i ω) ^ 2 ∂Q = 1 / ((h : ℝ) - N - 1) ∧
    ∫ ω, KanVar.y2 N (fun i => X i ω) ^ 2 ∂Q =
      ((h : ℝ) + N - 7) / (((h : ℝ) - N - 1) * ((h : ℝ) - N + 1)) := by sorry

end KanCombine.Optimal
