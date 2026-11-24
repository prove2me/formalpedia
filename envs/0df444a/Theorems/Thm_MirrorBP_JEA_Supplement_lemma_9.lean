-- Prove2me | Theorems.Thm_MirrorBP_JEA_Supplement_lemma_9
-- name    : MirrorBP.JEA.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:47:55.919044+00:00
-- url     : https://prove2.me/theorems/6c1ab32e-17cf-42bf-aef7-10d2f97d4d72
-- title:
--   Lemma 9, Appendix B.3.2, appendix pp. 10–11 — the congestion function (24) satisfies Condition 3 with M₁ = Cm and the buffer-dependent M₂
-- statement:
--   Let $V$ be a finite set of $m=|V|>1$ nodes, $V_b\subseteq V$ a set of buffer-constrained nodes with scaled buffer sizes $\bar d_j\in(0,1)$ for $j\in V_b$ and $\bar d_j=1$ for $j\notin V_b$, with $\bar d_\Sigma=\sum_{j\in V}\bar d_j>1$. Write $\bar d_{\min}=\min_{j\in V}\bar d_j$ and $\bar d_g=\min\{1,\bar d_\Sigma-1\}$.
--
--   There are universal constants $C,c>0$ and $N\in\mathbb N$, independent of $m$, $\bar d$, $K$ and $\alpha$, such that for every such instance and every $\alpha>0$ the congestion function (24) satisfies the growth condition (Condition 3) with parameters $(\alpha,K_1,M_1,M_2)$, where
--   $$K_1=c\Big(m+\frac1\alpha+\frac1{\bar d_{\min}}+\frac1{\bar d_g}\Big)^N,\qquad M_1=Cm,\qquad M_2=C\,\frac1{\bar d_{\min}}\left(\frac{\bar d_\Sigma}{\min\{\bar d_\Sigma-1,1\}}\right)^{3/2}\sqrt m .$$
--
--   Applied with $\alpha=\alpha_{\min}$, this is the input that turns the general finite-buffer guarantee (Theorem 4) into Theorem 2.
--
--   **Formalization Note** "$K_1=\mathrm{poly}(m,\bar d,1/\alpha_{\min})$" is written as $c(m+1/\alpha+1/\bar d_{\min}+1/\bar d_g)^N$ with $c,N$ chosen before the instance. Condition 3 is the definition in `MirrorBP.JEA.Supplement.Growth`, with all clauses for $K>K_1$ at which the buffer sizes $\bar d_jK$ are whole numbers.
--
--   Differences from the source:
--   - reading: Condition 3 prints 'for any K > K₁' only in 1(a) and 2(a), takes 2(b) over q, q′ ∈ Ω and B(f) ⊆ Ω → every clause of Condition 3 is required for every K > K₁, over the normalized physical states, with the windows [q̄_j ± 1/K̃] inside (0, d̄_j); reason: (24) depends on K and fails 2(c), 2(d) for small K; the appendix verifies 2(b) as a sup over Ω_K; the window clause only excludes families for which the maxima of f_j′ in (43) and 2(c) are undefined
--   - reading: K₁ = poly(m, d̄, 1/α_min) → K₁ = c·(m + 1/α_min + 1/d̄_min + 1/d̄_g)^N with universal c, N, d̄_min = min_j d̄_j, d̄_g = min{1, ∑_j d̄_j − 1}; reason: the thresholds derived in Appendix B.3.3 (PDF 44–45) are polynomial in m, 1/α, 1/d̄_min, 1/d̄_g, and d̄_Σ ≤ m; a polynomial in the bounded entries d̄_j alone cannot express the blow-up as d̄_min or d̄_g tends to 0
--   - generalization: parameter α = α_min of an instance → every α > 0; reason: Condition 3 depends on the instance only through α; α_min > 0 is one value of α
--   - reading: buffer size d_j = d̄_j K (p. 21), with d̄_j ≜ d_j/K (p. 22) → hypothesis IntegralCapacity: every d̄_j K is a natural number; reason: a buffer size is a number of supply units; the model with K units exists exactly for these K, and 'q_j = d_j' (a full buffer) is then an exact equality
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, Appendix B.3.2, appendix pp. 10–11 (PDF 43–44), Lemma 9; constants as in the proof of Theorem 2, Appendix D, appendix p. 15 (PDF 48)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_Supplement_Buffer
import Definitions.Def_MirrorBP_JEA_Supplement_Growth

namespace MirrorBP.JEA.Supplement

open Finset

theorem lemma_9 :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (Vb : Finset V) (dbar : V → ℝ) (α : ℝ),
        1 < Fintype.card V → IsBufferProfile Vb dbar → 0 < α →
        Condition3 Vb dbar (fun K => congestion24 Vb dbar K) α
          (c * ((Fintype.card V : ℝ) + 1 / α + 1 / dMin dbar + 1 / dGap dbar) ^ N)
          (C * (Fintype.card V : ℝ))
          (C * (1 / dMin dbar) * (dSum dbar / min (dSum dbar - 1) 1) ^ ((3 : ℝ) / 2)
            * Real.sqrt (Fintype.card V)) := by sorry

end MirrorBP.JEA.Supplement
