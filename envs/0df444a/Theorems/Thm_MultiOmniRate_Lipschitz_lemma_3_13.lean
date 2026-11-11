-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_13
-- name    : MultiOmniRate.Lipschitz.lemma_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:24:46.65821+00:00
-- url     : https://prove2.me/theorems/d5822586-9787-45d6-8a09-8f3c82ff7620
-- title:
--   Lemma 3.13 — Algorithm 3: $\sup_\ell|\sum_t\langle w_{\ell,r}(q_t),e_{y_t}-q_t\rangle|\le\sum_t\langle w_t(q_t),e_{y_t}-q_t\rangle+2nu_J+C\sqrt n\sum_ju_j\sqrt{\log(2M_j)}$
-- statement:
--   Fix $n\ge1$ and $0<r\le1/2$, let $J=\lfloor\log_2(1/r)\rfloor$, $u_j=2^{-j}$, and let $\mathcal B_j$ ($j=0,\dots,J$) be uniform $u_j$-covers of $\{w_{\ell,r}:\ell\in\mathcal L_{\mathrm{All}}\}$ by continuous maps $\Delta_K\to[-2,2]^K$, with nondecreasing upper bounds $M_j\ge1$ on $|\mathcal B_j|$. There is an absolute constant $C$ such that Algorithm 3 outputs continuous tests $w_t:\Delta_K\to[-5,5]^K$ before observing $(q_t,y_t)$, and for every sequence of predictions and labels
--   $$\sup_{\ell\in\mathcal L_{\mathrm{All}}}\Big|\sum_{t=1}^n\langle w_{\ell,r}(q_t),e_{y_t}-q_t\rangle\Big|\le\sum_{t=1}^n\langle w_t(q_t),e_{y_t}-q_t\rangle+2nu_J+C\sqrt n\sum_{j=0}^Ju_j\sqrt{\log(2M_j)}.$$
--   The same bound holds when the residuals $e_{y_t}-q_t$ are replaced by arbitrary vectors of $\ell_1$ norm at most two, in both the updates and the inequality.
--
--   This is the chaining step that turns the covering bounds of Lemma 3.11 into an online decision learner.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: rounds $t=1,\dots,n$ → rounds $t=0,\dots,n-1$ (`Finset.range n` or `Fin n`); reason: index shift only
--   - generalization: covers "as in Algorithm 3" (with the size bounds of Lemma 3.11) → any uniform $u_j$-covers by continuous maps into $[-2,2]^K$, no size bound; reason: the inequality uses the sizes only through the $M_j$; the paper's covers are a special case
--   - encoding: "outputs continuous tests $w_t$ before observing $(q_t,y_t)$" → `chainOut` at round $t$ reads only rounds $<t$; a separate clause states continuity and the range $[-5,5]^K$ for every feedback sequence; reason: non-anticipation is structural
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 34, Lemma 3.13

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
import Definitions.Def_MultiOmniRate_Lipschitz_Learners

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_13.{u} : ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∀ (n : ℕ), 1 ≤ n → ∀ (r : ℝ), 0 < r → r ≤ 1 / 2 →
    ∀ (B : ℕ → Finset (Simplex K → Fin K → ℝ)),
      (∀ j ≤ chainJ r, IsUniformCover (B j) (smoothWClass.{u} K r) (chainU j) ∧
        ∀ b ∈ B j, Continuous b ∧ ∀ q k, |b q k| ≤ 2) →
    ∀ (M : ℕ → ℝ), (∀ j ≤ chainJ r, 1 ≤ M j ∧ ((B j).card : ℝ) ≤ M j) →
      (∀ i j, i ≤ j → j ≤ chainJ r → M i ≤ M j) →
      (∀ (fb : ℕ → Simplex K × (Fin K → ℝ)) (t : ℕ),
        Continuous (chainOut B n r fb t) ∧ ∀ q k, |chainOut B n r fb t q k| ≤ 5) ∧
      (∀ seq : ℕ → Simplex K × Fin K,
        (⨆ ℓ : AllLoss.{u} K, |∑ t ∈ Finset.range n,
            dot (smoothW r ℓ.ℓ.pr (seq t).1) (resid (seq t).2 (seq t).1)|) ≤
          ∑ t ∈ Finset.range n, dot
              (chainOut B n r (fun s => ((seq s).1, resid (seq s).2 (seq s).1)) t (seq t).1)
              (resid (seq t).2 (seq t).1) +
            2 * n * chainU (chainJ r) +
            C * Real.sqrt n * ∑ j ∈ Finset.range (chainJ r + 1),
              chainU j * Real.sqrt (Real.log (2 * M j))) ∧
      (∀ fb : ℕ → Simplex K × (Fin K → ℝ), (∀ t, l1 (fb t).2 ≤ 2) →
        (⨆ ℓ : AllLoss.{u} K, |∑ t ∈ Finset.range n, dot (smoothW r ℓ.ℓ.pr (fb t).1) (fb t).2|) ≤
          ∑ t ∈ Finset.range n, dot (chainOut B n r fb t (fb t).1) (fb t).2 +
            2 * n * chainU (chainJ r) +
            C * Real.sqrt n * ∑ j ∈ Finset.range (chainJ r + 1),
              chainU j * Real.sqrt (Real.log (2 * M j))) := by sorry

end MultiOmniRate.Lipschitz
