-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_lemma_2
-- name    : OfflineCMC.Minimax.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:12.427361+00:00
-- url     : https://prove2.me/theorems/57fc34bd-0b56-40df-bc12-4bea1219e8d6
-- title:
--   Lemma 2 — m/T − 1 < E[N^(l)_s] ≤ m·max{ζ1, 1 − ζ2} under Assumptions 1 and 2, and m/(2T) < E[N^(l)_s] when m ≥ 2T
-- statement:
--   Let $\{(X_i,a_i)\}$ be a controlled Markov chain. Suppose it satisfies Assumption 1 with constants $\zeta_1,\zeta_2$ and Assumption 2 with the integer $T>0$. Then for every state–control pair $(s,l)$ the expected number $\mathbb E[N^{(l)}_s]$ of visits at times $1,\dots,m$ satisfies
--   $$
--   \frac mT-1<\mathbb E\big[N^{(l)}_s\big]\le m\max\{\zeta_1,1-\zeta_2\}. \tag{3.3}
--   $$
--   In particular, if $m\ge 2T$, then
--   $$
--   \frac m{2T}<\mathbb E\big[N^{(l)}_s\big]\le m\max\{\zeta_1,1-\zeta_2\}. \tag{3.4}
--   $$
--
--   The lemma locates the mean of the visit counts. The concentration bound of Proposition 3 is centred at these two bounds.
--
--   **Formalization Note** The expectation is the Lebesgue integral of the real-valued count, which is bounded by $m$. Assumption 2 is the definition's encoding: almost surely finite, integrable return times, and an $\omega$-dependent witness $T'<T$ for the strict bound on the supremum of the conditional expectations at the previous visit time.
--
--   Differences from the source:
--   - generalization: Assumption 1 "for all times $i$" → Assumption 1 at the times $1\le i\le m$ only; reason: a weaker hypothesis, implied by the paper's, so the statement specializes to the source's
--   - reading: first hitting time $\min\{n:(X_n=s,a_n=l),(X_j\ne s,a_j\ne l)\ \forall\,0<j<n\}$ → the first time $n\ge1$ with $(X_n,a_n)=(s,l)$; reason: "$(X_j\ne s,a_j\ne l)$" read as $(X_j,a_j)\ne(s,l)$, as in the recursive clause "$X_j\ne s\cup a_j\ne l$"
--   - encoding: $\sup_{s,l,i}\mathbb E[\tau^{(i)}_{s,l}\mid\mathcal F_{H_{i-1}}]<T$ a.e. → return times a.s. finite and integrable, and a.e. an $\omega$-dependent $T'<T$ bounding every conditional expectation; reason: the paper's bound implies finiteness and integrability, and a supremum is $<T$ exactly when some $T'<T$ bounds it
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 10, Lemma 2, eqs. (3.3)–(3.4); Assumptions 1–2, p. 10

import Mathlib
import Definitions.Def_OfflineCMC_Minimax_CMC
import Definitions.Def_OfflineCMC_Minimax_Model

namespace OfflineCMC.Minimax

open MeasureTheory

theorem lemma_2 {d k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : CMC d k μ) (m : ℕ) (ζ₁ ζ₂ : ℝ) (T : ℕ)
    (h1 : C.Assumption1 m ζ₁ ζ₂) (h2 : C.Assumption2 T) (s : Fin d) (l : Fin k) :
    ((m : ℝ) / (T : ℝ) - 1 < ∫ ω, (C.count m l s ω : ℝ) ∂μ ∧
        ∫ ω, (C.count m l s ω : ℝ) ∂μ ≤ (m : ℝ) * zetaMax ζ₁ ζ₂) ∧
      (2 * (T : ℝ) ≤ (m : ℝ) →
        (m : ℝ) / (2 * (T : ℝ)) < ∫ ω, (C.count m l s ω : ℝ) ∂μ ∧
          ∫ ω, (C.count m l s ω : ℝ) ∂μ ≤ (m : ℝ) * zetaMax ζ₁ ζ₂) := by sorry

end OfflineCMC.Minimax
