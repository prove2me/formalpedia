-- Prove2me | Theorems.Thm_HardCoreBochner_log_inv_muMin_le
-- name    : HardCoreBochner.log_inv_muMin_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:32.414533+00:00
-- url     : https://prove2.me/theorems/90af01be-3035-4168-8816-bdd102e4e926
-- title:
--   Proof of Theorem 1.1 — $\log(1/\mu_{\min})\le O(n\log(1+1/\lambda))$
-- statement:
--   There is an absolute constant $C_0>0$ with the following property. Let $G$ be a finite graph on $n$ vertices, $\delta\in(0,1)$ and $\lambda>0$, with $-\lambda_{\min}(A_G)-1>0$ and
--   $$\lambda\le\frac{1-\delta}{-\lambda_{\min}(A_G)-1}$$
--   (the hypotheses of Theorem 1.1). Then, for the hard-core model $\mu=\mu_{G,\lambda}$,
--   $$\log\big(4/\mu_{\min}\big)\le C_0\,n\log\big(1+1/\lambda\big).$$
--   Since $\log(1/\mu_{\min})\le\log(4/\mu_{\min})$, this gives the paper's bound $\log(1/\mu_{\min})\le O(n\log(1+1/\lambda))$, which completes the proof of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: log(1/µ_min) ≤ O(n log(1 + 1/λ)) → log(4/µ_min) ≤ C₀ n log(1 + 1/λ); reason: log(4/µ_min) ≥ log(1/µ_min), so the Lean bound implies the printed one with the same C₀; 4/µ_min is the quantity of the preceding step
--   - encoding: O(·) → ∃ C₀ > 0 chosen before V, G, δ and λ; reason: the O(·) is one absolute constant
--   - reading: the step stated inside the proof of Theorem 1.1, without listing its hypotheses → the hypotheses of Theorem 1.1: 0 < δ < 1, 0 < λ, 0 < −lamMin G − 1, λ ≤ (1 − δ)/(−lamMin G − 1); reason: the step is part of that proof and is false without them (G = K₂, λ → ∞); the positive denominator is read as for Theorem 1.1
--   - encoding: a finite graph on any vertex set → V : Type (universe 0); reason: every finite set is in bijection with some Fin n, which lives in Type; the constant is chosen before V, so no instance is lost
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Definitions.Def_mm_coupling
import Definitions.Def_HardCoreBochner_lamMin
import Definitions.Def_HardCoreBochner_muMin

namespace HardCoreBochner

/-- **The bound on `µ_min`.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.1, p.4: "Bounding log(1/µmin) ≤ O(n log(1 +
1/λ)) completes the proof."

There is an absolute constant `C₀ > 0` such that for every finite graph `G` on `n` vertices,
`δ ∈ (0,1)` and `λ > 0` with `−λ_min(A_G) − 1 > 0` and `λ ≤ (1 − δ)/(−λ_min(A_G) − 1)` (the
hypotheses of Theorem 1.1), `log(4/µ_min) ≤ C₀ n log(1 + 1/λ)`.

**Formalization Note** `C₀` is chosen before the graph and the parameters. The Lean bounds
`log(4/µ_min) = log 4 + log(1/µ_min)`, the quantity that `tmix_le_of_gap` produces; it implies the
printed `log(1/µ_min)` bound. The bound is false for unbounded `λ` (e.g. `G = K₂`), so it is stated
under the hypotheses of Theorem 1.1, which bound `λ` by `1 + √2` (`lamMin_le_neg_sqrt_two`). -/
theorem log_inv_muMin_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (δ lam : ℝ), 0 < δ → δ < 1 → 0 < lam → 0 < -lamMin G - 1 →
        lam ≤ (1 - δ) / (-lamMin G - 1) →
        Real.log (4 / muMin (MarkovMixing.hardcoreDist G lam)) ≤
          C₀ * Fintype.card V * Real.log (1 + 1 / lam) := by sorry

end HardCoreBochner
