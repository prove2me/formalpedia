-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_4
-- name    : GenCountSampleLLL.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:42.12119+00:00
-- url     : https://prove2.me/theorems/6add1922-5af0-4328-8599-f8714ad4290d
-- title:
--   Lemma 6.4, p.22 — $\pi=\tilde w/M$ is stationary for $K^\beta_{\mathcal D,a}$ and $K$ is reversible
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$, let $a\in\mathcal D\subseteq\mathcal C$ and $0<\beta<1$, and let $K=K^\beta_{\mathcal D,a}$. The distribution
--   $$
--   \pi(X)=\frac{\tilde w(X)}M\qquad(X\in\mathsf S(\mathcal D,a))
--   $$
--   is stationary for $K$, and $K$ is reversible with respect to $\pi$: $\pi(X)K(X,Y)=\pi(Y)K(Y,X)$ for all states.
--
--   This identifies the limit of the insertion chain and makes the spectral and flow arguments available.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: K = K^β_{𝒟,a} defined "for 0 < β < 1" (p.19) → hypothesis 0 < β < 1; reason: the range of the definition
--   - encoding: "stationary", "reversible" → `MarkovMixing.IsStationary` (π a probability vector with πK = π) and `MarkovMixing.DetailedBalance`; reason: the standard notions, published definitions
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 6.4, p.22

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_mm_basic

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Lemma 6.4, p.22 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`. For `a ∈ D ⊆ C`
and `0 < β < 1`, the distribution `π(X) = w̃(X)/M` on `S(D, a)` is stationary for `K = K^β_{D,a}`,
and `K` is reversible with respect to `π`.

**Formalization Note.** Stationarity is `MarkovMixing.IsStationary` (π is a probability vector and
`πK = π`) and reversibility is detailed balance `π(X)K(X,Y) = π(Y)K(Y,X)`. -/
theorem lemma_6_4 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    MarkovMixing.IsStationary (I.Kker β D a) (I.piDist β D a) ∧
      MarkovMixing.DetailedBalance (I.Kker β D a) (I.piDist β D a) := by sorry

end GenCountSampleLLL
