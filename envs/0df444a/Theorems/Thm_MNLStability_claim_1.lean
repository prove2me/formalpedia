-- Prove2me | Theorems.Thm_MNLStability_claim_1
-- name    : MNLStability.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:24.795129+00:00
-- url     : https://prove2.me/theorems/e2f2f238-9f8c-446b-98b4-126a721b0132
-- title:
--   Claim 1 — the range of $\varphi$ and of $\sum_{\ell\in\Lambda}R_\ell$ (corrected: $\varepsilon\le1$)
-- statement:
--   **Setting (§4.3).** $I$ is a set of products with uniform preference weights, indexed by non-increasing prices; $H$ is a $(1+\varepsilon)$-spaced subset of $[C]$ with $0$ added, $L=|H|$; $U^{\mathrm{step}}$ stocks at most $C$ units, its levels on $I$ lie in $H$ and are non-increasing in the price order; $I_\ell$, $R_\ell$, $\ell_{\min}$ and $\Lambda$ are as in §4.3, and some $R_\ell>0$.
--
--   Let $i_0$ be the first product of $I_{\ell_{\min}}$ (its price $r_{\min I_{\ell_{\min}}}$ is the largest in the interval) and $\varphi=\Pr[I^{U^{\mathrm{step}}}_{(i_0,1)}=1]$. In the sampling-amenable regime $w_{\max}>\varepsilon w_0/n$, with $0<\varepsilon\le1$:
--
--   $$\varphi\in\Bigl[\frac{\varepsilon}{2n\Delta}\Pr[M\ge1],\ \Pr[M\ge1]\Bigr]\qquad\text{and}\qquad\sum_{\ell\in\Lambda}R_\ell\in\bigl[\varphi\,r_{\min I_{\ell_{\min}}},\ C\varphi\,r_{\min I_{\ell_{\min}}}\bigr].$$
--
--   The two intervals locate the quantities that the guessing procedure of §4.3 enumerates.
--
--   Differences from the source:
--   - generalization: U^step = (U ↩_I V^step) of Lemma 7, for a vector U with at most C units → any U^step with at most C units whose levels on I lie in H and are non-increasing in the price order; reason: the proof uses only these properties of U^step; the vector of Lemma 7 is one such
--   - correction: ε > 0 (the accuracy level) → 0 < ε ≤ 1; reason: for ε > 1 the lower bound on φ fails: n = 1, w₁ = 1, w₀ = 1/10, ε = 4 (so w_max = 1 > εw₀/n = 2/5), M ≡ 1, C = 1, H = {0, 1}, U^step = (1): φ = 1/1.1 < ε/(2nΔ) = 2; the proof's step w₀ + nw_max ≤ 2nw_max/ε needs ε ≤ 1
--   - encoding: the standing assumption of §2.3 ("in the remainder of this paper, we operate under … w_max > εw₀/n") → hypothesis ε·w₀/n < w_max; reason: the assumption is stated once for the rest of the paper
--   - encoding: ℓ_min and the first product min I_{ℓ_min} of the interval → the largest level with positive contribution, and any product i₀ of that interval with the largest price; reason: levels decrease with ℓ; products of an interval share weight and stock, so φ is the same for all of them, and the first product has the largest price
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Claim 1, p.21; proof App. A.4, pp.45–46; regime §2.3, p.13

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam

namespace MNLStability

/-- **Claim 1** (SSRN:3498325, p.21; proof App. A.4, pp.45–46). Setting of §4.3 (p.20): `I` is a set of
products with uniform preference weights, listed by `ord` by non-increasing price; `H` is a
`(1 + ε)`-spaced subset of `[C]` with `0` added; `U^step` stocks at most `C` units, its levels on
`I` lie in `H` and are non-increasing along `ord`; the interval `I_ℓ` is the set of products of
`I` at level `H(ℓ)`, with revenue contribution `R_ℓ`; some `R_ℓ > 0`, `ℓ_min` is the least such
index, and `Λ = {ℓ : R_ℓ ≥ (ε/L)·R_{ℓ_min}}`, `L = |H|`.

Let `i₀` be the first product of `I_{ℓ_min}` (one of largest price `r_{min I_{ℓ_min}}` in it) and
`φ = Pr[I^{U^step}_{(i₀,1)} = 1]`. In the sampling-amenable regime `w_max > ε·w₀/n`, `ε ≤ 1`
(§2.3, p.13):
$$φ ∈ [ε/(2nΔ)·Pr[M ≥ 1], Pr[M ≥ 1]] \quad\text{and}\quad Σ_{ℓ∈Λ} R_ℓ ∈ [φ·r_{min I_{ℓ_min}}, C·φ·r_{min I_{ℓ_min}}].$$ -/
theorem claim_1 {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (Ustep : Fin n → ℕ) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep) (hnorm : norm1 Ustep ≤ C)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (hε1 : ε ≤ 1) (hreg : ε * wts.w0 / n < wts.wmax)
    (i₀ : Fin n) (hi₀ : i₀ ∈ lev I Ustep (hMin wts r pM I H Ustep))
    (hi₀max : ∀ j ∈ lev I Ustep (hMin wts r pM I H Ustep), r j ≤ r i₀) :
    ε / (2 * n * wts.Delta) * probMpos pM ≤ unitProb wts pM Ustep i₀ 1 ∧
      unitProb wts pM Ustep i₀ 1 ≤ probMpos pM ∧
      unitProb wts pM Ustep i₀ 1 * r i₀ ≤ ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h ∧
      ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h ≤
        C * unitProb wts pM Ustep i₀ 1 * r i₀ := by sorry

end MNLStability
