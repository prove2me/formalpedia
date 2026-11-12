-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_B_2
-- name    : NetUnrelEst.Main.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:24.716093+00:00
-- url     : https://prove2.me/theorems/82b62549-f6ad-4b7b-a1f5-a9390e62da07
-- title:
--   Lemma B.2 — ‖T_t f‖₂ ≤ ‖f‖_{1+t} for increasing f, and its light-edge-count version (63)
-- statement:
--   Consider independent failure bits with probabilities $p_e\in[0,1]$, a nonnegative function $f$ of the failure bits that is nondecreasing in the set of failed edges, and $0\le t\le1$. Let $T_tf=\mathbb E(f\mid O_t)$, where $O_t$ records the working edges observed by time $t$ (an edge stays unobserved with probability $p_e^{t}$). Then
--   $$\|T_tf\|_2\le\|f\|_{1+t}.\tag{62}$$
--   For every $0<\eta<1$, if light-edge counts are chosen as in §2.6 and followed by observations through time $t$ (the information $S_t$), then
--   $$\mathbb E\big[\mathbb E(f\mid S_t)^2\big]\le\|f\|_{1+R(t)}^2,\qquad R(t)=t+\eta(1-t).\tag{63}$$
--
--   The norms of $f$ are taken under the product law of the failure bits and the norm of $T_tf$ under the induced law of the observations. This is a hypercontractive inequality for observing working edges. It gives the bound $\mathbb EU_t^2\le u^{2/(1+R(t))}$ of (31) on the conditional unreliability, which the variance analysis uses before any cut search succeeds.
--
--   **Formalization Note.** $\|f\|_r^r=\mathbb E f^r$ and $\|T_tf\|_2^2=\mathbb E[\mathbb E(f\mid O_t)^2]$ are finite sums. In (63) the counts are drawn for every edge with $p_e>0$ ($p_e=1$ gives $N_e=0$, a certain failure), and a deterministic working bit ($p_e=0$) is kept deterministic.
--
--   Differences from the source:
--   - encoding: 'fix any deterministic bits and choose independent light-edge counts' (App. B) → counts for every edge with p_e > 0 (for p_e = 1 the count law gives N_e = 0, Z_e = 1, a deterministic failure); Z_e = 0 for p_e = 0; reason: deterministic bits get the deterministic law either way, so the experiment is the paper's
--   - encoding: ‖T_t f‖₂, ‖f‖_r, E[E(f | S_t)²] → finite sums over observation sets, failure sets and count choices; ‖f‖_r = (E f^r)^{1/r}; reason: the laws are finite; same quantities
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 34, Lemma B.2

import Mathlib
import Definitions.Def_NetUnrelEst_Main_Contraction

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma B.2.** For independent failure bits with probabilities `p ∈ [0,1]^m`, every
nonnegative increasing function `f` of the failure bits and every `0 ≤ t ≤ 1`,
`‖T_t f‖₂ ≤ ‖f‖_{1+t}` (62); and for the light-edge counts (any `0 < η < 1`) followed by
observations through time `t`, `E[E(f | S_t)²] ≤ ‖f‖²_{1+R(t)}`, `R(t) = t + η(1 − t)` (63).
Sun 2027, p. 34, Lemma B.2. -/
theorem lemma_B_2 {m : ℕ} (p : Fin m → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (f : Finset (Fin m) → ℝ) (hf0 : ∀ F, 0 ≤ f F) (hfm : IsIncreasing f) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    Real.sqrt (ordObsSecondMoment p t f) ≤ lpNormPow p f (1 + t) ^ (1 / (1 + t)) ∧
    ∀ η : ℝ, 0 < η → η < 1 →
      repObsSecondMoment η p t f ≤
        lpNormPow p f (1 + (t + η * (1 - t))) ^ (2 / (1 + (t + η * (1 - t)))) := by sorry

end NetUnrelEst.Main
