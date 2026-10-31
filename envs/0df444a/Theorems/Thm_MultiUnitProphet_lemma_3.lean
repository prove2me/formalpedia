-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_3
-- name    : MultiUnitProphet.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:59.049984+00:00
-- url     : https://prove2.me/theorems/9dfaa84d-7e24-456b-bc24-7358c3e9630a
-- title:
--   Lemma 3 — the worst-case ratio over $n$ buyers equals the (GenBern) optimum $\phi^\star_k(n)$
-- statement:
--   Let $0<k<n$. The worst-case competitive ratio of the pricing scheme over instances with $n$ buyers equals the optimal value $\phi^\star_k(n)$ of (GenBern : $\min\phi$ s.t. $\delta=\mu=\phi$):
--
--   1. the minimum of (GenBern) over $n$ biases in $[0,1]$ is attained and equals $\phi^\star_k(n)$;
--   2. over atomless instances $\mathcal F$ with $n$ buyers and prices $\pi$ with $\delta_k(X_\pi)=\mu_k(X_\pi)$, the least value of $\phi_k(\pi,\mathcal F)=\delta_k(X_\pi)$ is $\phi^\star_k(n)$:
--
--   $$\phi_k(\boldsymbol\pi)=\inf_{\mathcal F}\phi_k(\boldsymbol\pi,\mathcal F)=\phi^\star_k(n).$$
--
--   The reduction replaces each $F_t$ by a Bernoulli of bias $b_t=\mathbb P[v_t\ge\pi]$, which leaves $\delta_k$ and $\mu_k$ unchanged.
--
--   **Formalization Note** Both infima are stated as attained least values. Every balancing price $\pi$ is allowed; for an atomless instance all of them give the same value $\delta_k(X_\pi)$.
--
--   Differences from the source:
--   - reading: the worst-case competitive ratio ϕ_k(π) for a number n > k of customers equals ϕ⋆_k → for each fixed n > k, the least ratio over n-buyer instances equals phiStar k n; reason: φ⋆_k is defined with n Bernoullis and, for k ≥ 2, decreases strictly in n (k = 2: 0.6048 at n = 3, 0.5993 at n = 4), so an infimum over all n would differ
--   - generalization: the optimal value / the infimum (3.4) → IsLeast: the value is attained by some biases and by some instance and price; reason: attainment implies the equality of the infimum
--   - generalization: the scheme's selected price π(k, F) → every price π with δ_k(X_π) = µ_k(X_π); reason: for atomless instances all balancing prices give the same δ_k(X_π), so this is the scheme's value
--   - encoding: a supply k > 0 → 0 < k; reason: same condition
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 3, p.10

import Mathlib
import Definitions.Def_MultiUnitProphet_Model
import Definitions.Def_MultiUnitProphet_GenBern

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 3: the worst-case ratio over `n` buyers equals the GenBern optimum `φ⋆_k`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 3, p.10: "For any supply k > 0, number n > k of customers, the worst-case
competitive ratio ϕk(π) of our pricing scheme is equal to the optimal value of
(GenBern : min ϕ s.t. δ = µ = ϕ), ϕ⋆k."

For `0 < k < n`: (1) the minimum of (GenBern : min φ s.t. δ = µ = φ) over `n` biases is attained and
equals `φ⋆_k(n)`; (2) the least value of `φ_k(π, F) = δ_k(X_π)` over atomless instances `F` with `n`
buyers and prices `π` with `δ_k(X_π) = µ_k(X_π)` is `φ⋆_k(n)`.

**Formalization Note.** `φ⋆_k` depends on `n`, so the lemma is read for each fixed `n`. The
infimum (3.4) is stated as an attained least value (`IsLeast`). `π` ranges over every price with
`δ_k(X_π) = µ_k(X_π)`; for an atomless instance all such prices give the same `δ_k(X_π)`. -/
theorem lemma_3 (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    IsLeast (genBernValues k n) (phiStar k n) ∧
    IsLeast {φ : ℝ | ∃ F : Fin n → Measure ℝ, IsInstance F ∧ (∀ t, NullSingletonClass (F t)) ∧
        ∃ p : ℝ, delta k F p = mu k F p ∧ delta k F p = φ} (phiStar k n) := by sorry

end MultiUnitProphet
