-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_16
-- name    : MultiOmniRate.Lipschitz.lemma_3_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:24:54.985572+00:00
-- url     : https://prove2.me/theorems/c5cd3970-a2d5-41b5-a6f4-e21238ddf9e0
-- title:
--   Lemma 3.16 — Algorithm 4: regret $C_Knr+C_K\sqrt n(\sqrt{\log(2N)}+\{1;\log(2/r);r^{-(K-3)/2}\})$
-- statement:
--   Fix $K\ge2$, $n\ge1$, $0<r\le1/2$ and a hypothesis class $\mathcal H$ of size $N\ge1$, and run Algorithm 4 with covers $\mathcal B_j\subseteq\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ as in Lemma 3.15. There is $C_K$, depending only on $K$ (and on the constant of the cover sizes), such that for every sequence of contexts, predictions and labels
--   $$\sup_{g\in\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H}\Big|\sum_{t=1}^n\langle g(x_t),e_{y_t}-q_t\rangle\Big|\le\sum_{t=1}^n\langle g_t(x_t),e_{y_t}-q_t\rangle+C_Knr+C_K\sqrt n\Big(\sqrt{\log(2N)}+\begin{cases}1,&K=2,\\ \log(2/r),&K=3,\\ r^{-(K-3)/2},&K\ge4\end{cases}\Big).\quad(3.5)$$
--
--   This is the hypothesis learner that, with the decision learner, proves the main theorem.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: rounds $t=1,\dots,n$ → rounds $t=0,\dots,n-1$ (`Finset.range n` or `Fin n`); reason: index shift only
--   - generalization: covers "as in Lemma 3.15" (its constant $C_K$) → admissible covers with $\log(2|\mathcal B_j|)\le C_{\mathrm{cov}}u_j^{-(K-1)}+\log(2N)$ for every constant $C_{\mathrm{cov}}>0$, with $C_K$ chosen after $C_{\mathrm{cov}}$; reason: Lemma 3.15's constant is one admissible $C_{\mathrm{cov}}$; the paper's $C_K$ inherits that constant
--   - encoding: a hypothesis class of size $N$ → a family $h:\mathrm{Fin}\,N\to(\mathcal X\to\Delta_K)$ (repetitions allowed); reason: a class of at most $N$ hypotheses
--   - encoding: $\ell\in\mathcal L_{\mathrm{Lip}}$ in $\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ → pairs $(\ell,\mathrm{BR}_\ell)$ of `LLip K`; the test $x\mapsto\Delta\ell(h(x))$ uses $\ell$ only; reason: every Lipschitz loss has a measurable best response, so the class of tests is the same
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), pp. 36–37, Lemma 3.16 and (3.5)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_16 : ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∀ (Ccov : ℝ), 0 < Ccov →
    ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type*) (N : ℕ), 1 ≤ N → ∀ (h : Fin N → X → Simplex K)
      (n : ℕ), 1 ≤ n → ∀ (r : ℝ), 0 < r → r ≤ 1 / 2 →
    ∀ (B : ℕ → Finset (X → Fin K → ℝ)), Alg4Covers K h r Ccov B →
    ∀ seq : ℕ → X × Simplex K × Fin K,
      (⨆ g : testClass (LLip K) (Set.range h), |∑ t ∈ Finset.range n,
          dot ((g : X → Fin K → ℝ) (seq t).1) (resid (seq t).2.2 (seq t).2.1)|) ≤
        ∑ t ∈ Finset.range n, dot
            (chainOut B n r (fun s => ((seq s).1, resid (seq s).2.2 (seq s).2.1)) t (seq t).1)
            (resid (seq t).2.2 (seq t).2.1) +
          C * n * r + C * Real.sqrt n * (Real.sqrt (Real.log (2 * N)) + hypBracket K r) := by sorry

end MultiOmniRate.Lipschitz
