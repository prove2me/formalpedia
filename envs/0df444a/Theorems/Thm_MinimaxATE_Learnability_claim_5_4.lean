-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_claim_5_4
-- name    : MinimaxATE.Learnability.claim_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:00:45.980794+00:00
-- url     : https://prove2.me/theorems/c80873cf-59c8-4cf5-a7a6-65d3abfdecc3
-- title:
--   Claim 5.4 — two priors on $(q,s,t)$ with a common $q$-marginal, separated $E[qh]$ and matching mixed moments of $qv$ up to degree $L$
-- statement:
--   For signs $s,t\in\{\pm1\}$ and parameters $a,d,r,e$ write $p_s=a+sd$, $m_t=r+te$, $h(s,t)=(1+t)e$ and
--   $$v(s,t)=\big(p_sm_t,\ p_s(1-m_t),\ (1-p_s)(r-e),\ (1-p_s)(1-r+e)\big).$$
--   Here $a,d,r,e$ are the parameters of a symmetric shattering witness (Definition 6) for classes with values in $[0,1]$: $a>0$, $0\le d\le a$, $a+d\le1$, $0\le e\le r$, $r+e\le1$. Let $u>0$, $\gamma\in[0,e]$, let $L\ge2$ be an integer, $\lambda=L^2u$, and let $A<4$ ($A\ne0$) be a constant for which Lemma 5.5 holds at $(u,L)$, i.e. some signed measure on $[u,\lambda]$ has the four properties of Lemma 5.5 with this $A$. Then there are probability measures $\mu_+,\mu_-$ on $(q,s,t)\in\mathbb R_{\ge0}\times\{-1,1\}^2$ such that
--   1. they have the same $q$-marginal, and under either measure $0\le q\le\lambda$ a.s., $E_\pm q=u$, $E_\pm[qh]\le2\gamma u$, $E_\pm[qh^2]\le2\gamma u$;
--   2. $E_{\mu_+}[qh]-E_{\mu_-}[qh]=\dfrac{2u\gamma}{A}\,\dfrac da$;
--   3. all mixed moments of the vector $qv$ of total degree at most $L$ agree: for every multi-index $\alpha\in\mathbb N_0^4$ with $|\alpha|\le L$,
--   $$E_{\mu_+}\Big[\prod_{\ell=1}^4(qv_\ell)^{\alpha_\ell}\Big]=E_{\mu_-}\Big[\prod_{\ell=1}^4(qv_\ell)^{\alpha_\ell}\Big].$$
--
--   This is the one-coordinate hard instance of the lower bound: two priors whose observable moments agree while the treatment effects differ.
--
--   **Formalization Note.** Measures live on `ℝ × Bool × Bool` with signs read through `pm`; "on $\mathbb R_{\ge0}$" is the almost-sure bound $0\le q$. Expectations are Bochner integrals of functions that are polynomial in $q$, hence integrable since $q$ is a.s. bounded.
--
--   Differences from the source:
--   - reading: "parameters a, d, r, e" → a > 0, 0 ≤ d ≤ a, a + d ≤ 1, 0 ≤ e ≤ r, r + e ≤ 1; reason: they are a shattering witness of Definition 6 for classes in [c, 1−c] and [0, 1] (p. 32); the claim's d/a and its bounds on h need exactly this range.
--   - reading: λ, L and "A < 4", not defined in the claim → λ = L²u with an integer L ≥ 2, and A < 4 (A ≠ 0) any value for which Lemma 5.5 holds at (u, L); reason: the claim takes them from Lemma 5.5, whose measure the proof uses (p. 37); for an arbitrary A < 4 the separation in property 2 contradicts property 1.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 32 (PDF 34), Claim 5.4; restated and proved p. 36-38 (PDF 38-40)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering

open MeasureTheory BartlettNN.Margin

namespace MinimaxATE.Learnability

theorem claim_5_4 (a d r e : ℝ) (ha : 0 < a) (hd : 0 ≤ d) (had : d ≤ a) (had1 : a + d ≤ 1)
    (he : 0 ≤ e) (hre : e ≤ r) (hre1 : r + e ≤ 1)
    (u : ℝ) (hu : 0 < u) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγe : γ ≤ e)
    (L : ℕ) (hL : 2 ≤ L) (A : ℝ) (hA0 : A ≠ 0) (hA : A < 4)
    (hξ : ∃ q w : Fin L → ℝ, (∀ j, q j ∈ Set.Icc u ((L : ℝ) ^ 2 * u)) ∧ ∑ j, |w j| ≤ 1 ∧
      ∑ j, q j * |w j| = u ∧ ∑ j, q j * w j = u / A ∧
      ∀ h : ℕ, 2 ≤ h → h ≤ L → ∑ j, q j ^ h * w j = 0) :
    let ps : Bool → ℝ := fun s => a + pm s * d
    let mt : Bool → ℝ := fun t => r + pm t * e
    let hfun : ℝ × Bool × Bool → ℝ := fun w => (1 + pm w.2.2) * e
    let v : ℝ × Bool × Bool → Fin 4 → ℝ := fun w =>
      ![ps w.2.1 * mt w.2.2, ps w.2.1 * (1 - mt w.2.2), (1 - ps w.2.1) * (r - e),
        (1 - ps w.2.1) * (1 - r + e)]
    ∃ μp μm : Measure (ℝ × Bool × Bool), IsProbabilityMeasure μp ∧ IsProbabilityMeasure μm ∧
      μp.map Prod.fst = μm.map Prod.fst ∧
      (∀ μ ∈ ({μp, μm} : Set (Measure (ℝ × Bool × Bool))),
        (∀ᵐ w ∂μ, 0 ≤ w.1 ∧ w.1 ≤ (L : ℝ) ^ 2 * u) ∧
        ∫ w, w.1 ∂μ = u ∧
        ∫ w, w.1 * hfun w ∂μ ≤ 2 * γ * u ∧
        ∫ w, w.1 * hfun w ^ 2 ∂μ ≤ 2 * γ * u) ∧
      (∫ w, w.1 * hfun w ∂μp) - ∫ w, w.1 * hfun w ∂μm = (2 * u * γ / A) * (d / a) ∧
      ∀ α : Fin 4 → ℕ, ∑ ℓ, α ℓ ≤ L →
        ∫ w, ∏ ℓ, (w.1 * v w ℓ) ^ (α ℓ) ∂μp = ∫ w, ∏ ℓ, (w.1 * v w ℓ) ^ (α ℓ) ∂μm := by sorry

end MinimaxATE.Learnability
