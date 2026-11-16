-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_B_7
-- name    : KMPMixing.Supplement.theorem_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:57:37.918251+00:00
-- url     : https://prove2.me/theorems/0229e944-da0e-4ddf-8a67-5c443d717bf3
-- title:
--   Theorem B.7 — labeled parallel KMP chain: $\mathrm{TV}\le\frac{t\sqrt d}{2}(2/3)^{k/2}$
-- statement:
--   Let $d\ge2$ be even and $t,k$ positive integers, and let $M_{\mathrm{LPKMP}}$ be the labeled parallel KMP chain on $\Omega=[d]^t$, with stationary distribution $\pi_{\mathrm{LPKMP}}(x)=\prod_{i=1}^d\#_i(x)!/(t!\binom{t+d-1}{d-1})$ (Lemma B.3). For every initial state $x^{(0)}\in\Omega$,
--   $$
--   \big\|M^k_{\mathrm{LPKMP}}(x^{(0)},\cdot)-\pi_{\mathrm{LPKMP}}\big\|_{\mathrm{TV}}\le\frac{t\sqrt d}{2}\Big(\frac23\Big)^{k/2}.
--   $$
--
--   Through Lemma B.4 the bound passes to the parallel KMP chain, which gives Theorem 6.15.
--
--   **Formalization Note** $\Omega$ is `Fin t → Fin d`; $\pi_{\mathrm{LPKMP}}$ is the base mission's `KMPMixing.labeledStationary d t`; $(2/3)^{k/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: transition matrix M_LPKMP of Definition B.2 (procedure) → the matching average of the product over pairs of an indicator times ∫₀¹ p^a(1−p)^b dp; reason: the probability of each outcome of the procedure given the matching, by independence of the particles given p_{ij}
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem B.7, p.73 (PDF p.75); Definition B.2 and Lemma B.3, p.71 (PDF p.73)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_Supplement_labeledParallelKMP

namespace KMPMixing.Supplement

open MarkovMixing KMPMixing

/-- **Theorem B.7** (arXiv:2609.38044, p.73 (PDF p.75)). For an even integer `d ≥ 2` and positive
integers `t` and `k`, for every initial state `x^{(0)} ∈ Ω = [d]^t` of the labeled parallel KMP
chain,
`‖M^k_LPKMP(x^{(0)}, ·) − π_LPKMP‖_TV ≤ (t √d / 2) · (2/3)^{k/2}`,
where `π_LPKMP(x) = ∏_i #_i(x)! / (t! · C(t + d − 1, d − 1))` is the stationary distribution of
Lemma B.3.

**Formalization Note** `Ω` is `Fin t → Fin d`. `π_LPKMP` is the base mission's
`KMPMixing.labeledStationary d t` (Lemma B.3 gives the same formula as Lemma 3.4). `‖·‖_TV` is
`MarkovMixing.tvDist` of the row `rowDist`. `(2/3)^{k/2}` is a real power. -/
theorem theorem_B_7 {d : ℕ} (hd : Even d) (hd2 : 2 ≤ d) (t k : ℕ) (ht : 0 < t) (hk : 0 < k)
    (x₀ : Fin t → Fin d) :
    tvDist (rowDist (lpkmpChain d t) k x₀) (labeledStationary d t) ≤
      (t : ℝ) * Real.sqrt d / 2 * (2 / 3 : ℝ) ^ ((k : ℝ) / 2) := by sorry

end KMPMixing.Supplement
