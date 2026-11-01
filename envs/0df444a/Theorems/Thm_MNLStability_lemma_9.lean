-- Prove2me | Theorems.Thm_MNLStability_lemma_9
-- name    : MNLStability.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:04.425947+00:00
-- url     : https://prove2.me/theorems/d9faffb4-80e9-487a-b34b-1dabdd86cdfa
-- title:
--   Lemma 9 — the reconstructed step vector keeps a $(1-3\varepsilon)$ fraction
-- statement:
--   Setting of §4.3–4.5: $U$ stocks at most $C$ units; $U^{\mathrm{step}}$ agrees with $U$ outside $I$, satisfies the three properties of Lemma 7 with respect to $U$, and its levels on $I$ lie in the $(1+\varepsilon)$-spaced set $H$ and are non-increasing in the price order ($I$ has uniform weights and is indexed by non-increasing price); some $R_\ell>0$. Let the estimates satisfy
--
--   $$(1-\varepsilon)\sum_{\ell\in\Lambda}R_\ell\le\tilde R\le\sum_{\ell\in\Lambda}R_\ell,\qquad R_\ell-\tfrac{\varepsilon}{L}\tilde R\le\tilde{\mathcal R}_\ell\le R_\ell,\qquad E_\ell\le\tilde{\mathcal E}_\ell\le(1+\varepsilon)E_\ell$$
--
--   for $\ell\in\Lambda$ (guessing steps 1–3). Then the lengths $\tilde m$ of §4.4 exist and $\tilde U^{\mathrm{step}}=(U\hookleftarrow_I\tilde V^{\mathrm{step}})$ satisfies:
--
--   1. $\mathbb E[X_i^{\tilde U^{\mathrm{step}}}]\ge\mathbb E[X_i^U]$ for every product $i\notin I$;
--   2. $\sum_{i\in I}r_i\,\mathbb E[X_i^{\tilde U^{\mathrm{step}}}]\ \ge\ (1-3\varepsilon)\sum_{i\in I}r_i\,\mathbb E[X_i^U]$;
--   3. $\|\tilde U^{\mathrm{step}}\|_1\le\|U\|_1$.
--
--   Since $\tilde V^{\mathrm{step}}$ depends only on the guesses, enumerating the guesses yields an $I$-universal family (Theorem 3).
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: U^step = (U ↩_I ⌊U↑⌋_H) of Lemma 7 → any U^step agreeing with U outside I, with levels in H non-increasing in price order, that satisfies properties 1–3 of Lemma 7; reason: the proof (pp.23–24) uses only these properties; the vector of Lemma 7 is one such
--   - encoding: the estimates of guessing steps 1–3 (powers of 1 + ε, multiples of (ε/L)R̃) → any estimates within the windows of steps 1–3; reason: the proof uses only the windows; the guessed values are instances
--   - encoding: the existence of m̃ (Lemma 8) → the conclusion includes that the lengths exist; reason: as in Lemma 8
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 9, p.22; proof pp.23–24

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam
import Definitions.Def_MNLStability_greedyLengths

namespace MNLStability

/-- **Lemma 9** (SSRN:3498325, p.22; proof pp.23–24). Setting of §4.3–4.5: `U` stocks at most `C`
units; `U^step` agrees with `U` outside `I`, satisfies the three properties of Lemma 7, and its
levels on `I` lie in the `(1 + ε)`-spaced set `H` and are non-increasing along `ord` (the products
of `I`, uniform weights, by non-increasing price); some `R_ℓ > 0`. Let the estimates satisfy
`R̃ ∈ [(1 − ε)·Σ_{ℓ∈Λ} R_ℓ, Σ_{ℓ∈Λ} R_ℓ]` (guessing step 1), `R_ℓ − (ε/L)·R̃ ≤ R̃_ℓ ≤ R_ℓ` (step 2) and
`E_ℓ ≤ Ẽ_ℓ ≤ (1 + ε)·E_ℓ` (step 3) for `ℓ ∈ Λ`. Then the lengths `m̃` of §4.4 exist, and
`Ũ^step = (U ↩_I Ṽ^step)` satisfies:
1. `E[X_i^{Ũ^step}] ≥ E[X_i^U]` for every product `i ∉ I`;
2. `Σ_{i ∈ I} r_i E[X_i^{Ũ^step}] ≥ (1 − 3ε)·Σ_{i ∈ I} r_i E[X_i^U]`;
3. `‖Ũ^step‖₁ ≤ ‖U‖₁`. -/
theorem lemma_9 {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (U : Fin n → ℕ) (hU : norm1 U ≤ C)
    (Ustep : Fin n → ℕ) (hoff : ∀ i, i ∉ I → Ustep i = U i) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep)
    (h1 : ∀ i, i ∉ I → expX wts pM U i ≤ expX wts pM Ustep i)
    (h2 : (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM Ustep i)
    (h3 : norm1 Ustep ≤ norm1 U)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (R0 : ℝ) (Rt Et : ℕ → ℝ)
    (hR0 : (1 - ε) * ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h ≤ R0 ∧
      R0 ≤ ∑ h ∈ Lam wts r pM I H Ustep ε, Rlev wts r pM I Ustep h)
    (hRt : ∀ h ∈ Lam wts r pM I H Ustep ε,
      Rlev wts r pM I Ustep h - ε / H.card * R0 ≤ Rt h ∧ Rt h ≤ Rlev wts r pM I Ustep h)
    (hEt : ∀ h ∈ Lam wts r pM I H Ustep ε, ∀ i ∈ lev I Ustep h,
      expX wts pM Ustep i ≤ Et h ∧ Et h ≤ (1 + ε) * expX wts pM Ustep i) :
    ∃ ks : List ℕ,
      greedyLengths (ord.map r) ((lamList wts r pM I H Ustep ε).map fun h => Rt h / Et h) =
        some ks ∧
      (∀ i, i ∉ I →
        expX wts pM U i ≤ expX wts pM (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) i) ∧
      (1 - 3 * ε) * ∑ i ∈ I, r i * expX wts pM U i ≤
        ∑ i ∈ I, r i * expX wts pM (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) i ∧
      norm1 (swap I U (stepVec ord (lamList wts r pM I H Ustep ε) ks)) ≤ norm1 U := by sorry

end MNLStability
