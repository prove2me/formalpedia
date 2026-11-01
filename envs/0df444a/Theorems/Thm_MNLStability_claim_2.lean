-- Prove2me | Theorems.Thm_MNLStability_claim_2
-- name    : MNLStability.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:19.301753+00:00
-- url     : https://prove2.me/theorems/29ab1813-236f-4336-a339-d5e191831270
-- title:
--   Claim 2 — the range and monotonicity of the expected demands $E_\ell$
-- statement:
--   In the setting of §4.3 (as in Claim 1), let $i_0$ be the first product of $I_{\ell_{\min}}$, $\varphi=\Pr[I^{U^{\mathrm{step}}}_{(i_0,1)}=1]$, and for $\ell\in\Lambda$ let $E_\ell=\mathbb E[X_i^{U^{\mathrm{step}}}]$ for $i\in I_\ell$. Then:
--
--   1. $E_\ell\in\bigl[\tfrac{\varepsilon}{nL}\varphi,\ C\varphi\bigr]$ for every $\ell\in\Lambda$;
--   2. $E_{\ell_1}\ge E_{\ell_2}$ whenever $\ell_1<\ell_2$ in $\Lambda$.
--
--   These bounds justify the grid of guessing step 3 and the monotone guesses $\tilde E_\ell$.
--
--   Differences from the source:
--   - generalization: U^step = (U ↩_I V^step) of Lemma 7, for a vector U with at most C units → any U^step with at most C units whose levels on I lie in H and are non-increasing in the price order; reason: the proof uses only these properties of U^step; the vector of Lemma 7 is one such
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - encoding: E_ℓ = E[X_i^{U^step}] for i ∈ I_ℓ ("by symmetry … identical over all products") → the bounds stated for every product i of I_ℓ; reason: the products of an interval share weight and stock; same content
--   - encoding: ℓ_min and the first product of the interval → the largest level with positive contribution, and any product i₀ of that interval with the largest price; reason: levels decrease with ℓ; φ is the same for all products of the interval
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Claim 2, p.21; proof App. A.5, pp.46–47

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam

namespace MNLStability

/-- **Claim 2** (SSRN:3498325, p.21; proof App. A.5, pp.46–47). Setting of §4.3 as in Claim 1. Let
`i₀` be the first product of `I_{ℓ_min}` and `φ = Pr[I^{U^step}_{(i₀,1)} = 1]`, and for `ℓ ∈ Λ` let
`E_ℓ = E[X_i^{U^step}]` for `i ∈ I_ℓ`. Then:
1. `E_ℓ ∈ [(ε/(nL))·φ, C·φ]` for every `ℓ ∈ Λ`;
2. `E_{ℓ₁} ≥ E_{ℓ₂}` whenever `ℓ₁ < ℓ₂` (i.e. `H(ℓ₁) > H(ℓ₂)`). -/
theorem claim_2 {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (Ustep : Fin n → ℕ) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep) (hnorm : norm1 Ustep ≤ C)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (i₀ : Fin n) (hi₀ : i₀ ∈ lev I Ustep (hMin wts r pM I H Ustep))
    (hi₀max : ∀ j ∈ lev I Ustep (hMin wts r pM I H Ustep), r j ≤ r i₀) :
    (∀ h ∈ Lam wts r pM I H Ustep ε, ∀ i ∈ lev I Ustep h,
      ε / (n * H.card) * unitProb wts pM Ustep i₀ 1 ≤ expX wts pM Ustep i ∧
        expX wts pM Ustep i ≤ C * unitProb wts pM Ustep i₀ 1) ∧
      ∀ h₁ ∈ Lam wts r pM I H Ustep ε, ∀ h₂ ∈ Lam wts r pM I H Ustep ε, h₂ < h₁ →
        ∀ i₁ ∈ lev I Ustep h₁, ∀ i₂ ∈ lev I Ustep h₂,
          expX wts pM Ustep i₂ ≤ expX wts pM Ustep i₁ := by sorry

end MNLStability
