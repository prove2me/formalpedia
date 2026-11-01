-- Prove2me | Theorems.Thm_MNLStability_lemma_8
-- name    : MNLStability.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:32.632585+00:00
-- url     : https://prove2.me/theorems/b09d7631-74bc-4624-8dac-dcbba6653aa7
-- title:
--   Lemma 8 — the greedy interval lengths are under-estimates
-- statement:
--   In the setting of §4.3 (as in Claim 1), let $\ell_1<\dots<\ell_{|\Lambda|}$ be the elements of $\Lambda$ and let $\tilde{\mathcal R}_\ell\le R_\ell$ and $\tilde{\mathcal E}_\ell\ge E_\ell$ be estimates for $\ell\in\Lambda$. Let $\tilde m_{\ell_1}$ be the minimal index with $\sum_{i=1}^{\tilde m_{\ell_1}}r_i\ge\tilde{\mathcal R}_{\ell_1}/\tilde{\mathcal E}_{\ell_1}$, then $\tilde m_{\ell_2}$ the minimal index with $\sum_{i=\tilde m_{\ell_1}+1}^{\tilde m_{\ell_1}+\tilde m_{\ell_2}}r_i\ge\tilde{\mathcal R}_{\ell_2}/\tilde{\mathcal E}_{\ell_2}$, and so on. These minimal indices exist, and
--
--   $$\tilde m_{\ell_\lambda}\ \le\ m_{\ell_\lambda}=|I_{\ell_\lambda}|\qquad\text{for every }\lambda\in[|\Lambda|].$$
--
--   Differences from the source:
--   - generalization: U^step = (U ↩_I V^step) of Lemma 7, for a vector U with at most C units → any U^step with at most C units whose levels on I lie in H and are non-increasing in the price order; reason: the proof uses only these properties of U^step; the vector of Lemma 7 is one such
--   - generalization: the estimates of guessing steps 2–3 (R_ℓ − (ε/L)R̃ ≤ R̃_ℓ ≤ R_ℓ and E_ℓ ≤ Ẽ_ℓ ≤ (1 + ε)E_ℓ) → any estimates with R̃_ℓ ≤ R_ℓ and Ẽ_ℓ ≥ E_ℓ; reason: the induction of App. A.6 uses only these two inequalities; the guessed estimates are instances
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - reading: m̃_{ℓ_λ} "the minimal index for which …" (existence implicit) → the conclusion includes that the minimal indices exist; reason: the induction of App. A.6 shows the index m_{ℓ_λ} qualifies, so the minimum exists; the inequality presupposes it
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 8, p.22; proof App. A.6, pp.47–48

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam
import Definitions.Def_MNLStability_greedyLengths

namespace MNLStability

/-- **Lemma 8** (SSRN:3498325, p.22; proof App. A.6, pp.47–48). Setting of §4.3 as in Claim 1. Let
`ℓ₁ < ⋯ < ℓ_{|Λ|}` be the elements of `Λ`, and let `R̃_ℓ ≤ R_ℓ` and `Ẽ_ℓ ≥ E_ℓ` be estimates for
`ℓ ∈ Λ`. Let `m̃_{ℓ₁}` be the minimal index with `Σ_{i=1}^{m̃_{ℓ₁}} r_i ≥ R̃_{ℓ₁}/Ẽ_{ℓ₁}`,
`m̃_{ℓ₂}` the minimal index with `Σ_{i=m̃_{ℓ₁}+1}^{m̃_{ℓ₁}+m̃_{ℓ₂}} r_i ≥ R̃_{ℓ₂}/Ẽ_{ℓ₂}`, and so on.
These minimal indices exist, and `m̃_{ℓ_λ} ≤ m_{ℓ_λ} = |I_{ℓ_λ}|` for every `λ ∈ [|Λ|]`. -/
theorem lemma_8 {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (Ustep : Fin n → ℕ) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep) (hnorm : norm1 Ustep ≤ C)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (Rt Et : ℕ → ℝ) (hRt : ∀ h ∈ Lam wts r pM I H Ustep ε, Rt h ≤ Rlev wts r pM I Ustep h)
    (hEt : ∀ h ∈ Lam wts r pM I H Ustep ε, ∀ i ∈ lev I Ustep h, expX wts pM Ustep i ≤ Et h) :
    ∃ ks : List ℕ,
      greedyLengths (ord.map r) ((lamList wts r pM I H Ustep ε).map fun h => Rt h / Et h) =
        some ks ∧
      List.Forall₂ (fun k h => k ≤ (lev I Ustep h).card) ks (lamList wts r pM I H Ustep ε) := by sorry

end MNLStability
