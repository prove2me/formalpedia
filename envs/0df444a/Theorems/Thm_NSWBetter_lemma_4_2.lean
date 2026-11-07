-- Prove2me | Theorems.Thm_NSWBetter_lemma_4_2
-- name    : NSWBetter.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:10.298219+00:00
-- url     : https://prove2.me/theorems/47a0cc9e-3d1f-4a90-92fa-be07eea8da6a
-- title:
--   Lemma 4.2 — $\mathrm{ST}(x,i)\ge\mathrm{logNSW}(W)$ for the artificial instance
-- statement:
--   Let $v\ge0$ be additive valuations, $x$ a fractional allocation, and $D$ an ST rounding scheme for $x$ (Marginals and Cardinality, for buckets built in a non-increasing value order of each agent). Let $\Delta$ be feasible for $x$ and $D$ (Definition 4.1), and let $W$ be the round robin allocation of the artificial instance $I_{i,x}(\Delta)$. Then
--   $$\mathrm{ST}(x,i)=\mathbb E[\ln v_i(X_i)]\ \ge\ \mathrm{logNSW}(W).$$
--
--   This connects ST rounding to the round robin analysis of Section 3.
--
--   Differences from the source:
--   - encoding: valuations $v_i:2^G\to\mathbb R_{\ge0}$ → `v : Fin n → Fin m → ℝ`, $v\ge0$; reason: Lean convention; same instances
--   - reading: "assume without loss of generality $v_i(g_1)\ge\dots\ge v_i(g_m)$" for the buckets → every ranking $r$ by non-increasing value; reason: the source fixes the order only up to ties; the statement is made for each such order
--   - encoding: the random matching $M_{G(x)}$ and $\mathrm{ST}(x,i)$ → a finitely supported distribution $D$ on matchings, `STi` in `EReal` with $\ln0=-\infty$; reason: same values whenever finite
--   - encoding: $\mathrm{logNSW}(W)$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Lemma 4.2, p.17

import Mathlib
import Definitions.Def_NSWBetter_logNSWrr
import Definitions.Def_NSWBetter_IsFrac
import Definitions.Def_NSWBetter_IsValueOrder
import Definitions.Def_NSWBetter_IsSTScheme
import Definitions.Def_NSWBetter_STi
import Definitions.Def_NSWBetter_IsFeasibleDelta
import Definitions.Def_NSWBetter_artificial

namespace NSWBetter

/-- **Lemma 4.2 — ST rounding versus round robin.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Lemma 4.2, p.17: "Let x be a fractional allocation. Let Ii,x(∆) be the artificial instance of agent i for some ∆ that is feasible with respect to x. Let W be the round robin allocation of this instance Ii,x(∆). The following holds: ST(x, i) ≥ logNSW(W)."

For every ST rounding scheme `D` (Marginals and Cardinality for the buckets of `x` in a value order `r`) and every `Δ` feasible for `x` and `D` (Definition 4.1).

**Formalization Note.** Rationality of the scheme is not needed here: feasibility (b) is assumed directly. -/
theorem lemma_4_2 {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (x : Fin n → Fin m → ℝ) (hx : IsFrac x) (r : Fin n → Fin m ≃ Fin m) (hr : IsValueOrder v r)
    (D : Finset (Fin n × Fin m × Fin m) → ℝ) (hD : IsSTScheme r x D) (i : Fin n) (Δ : ℕ)
    (hΔ : IsFeasibleDelta r x D Δ) :
    logNSWrr Δ (artificial v x i Δ) ≤ STi v D i := by sorry

end NSWBetter
