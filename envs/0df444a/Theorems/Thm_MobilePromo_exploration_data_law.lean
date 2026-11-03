-- Prove2me | Theorems.Thm_MobilePromo_exploration_data_law
-- name    : MobilePromo.exploration_data_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:01.388442+00:00
-- url     : https://prove2.me/theorems/91cb3b54-8a34-4879-922b-cc1c6fbbd208
-- title:
--   pp.17, 20: the exploration data of BidAlloc are dominated by the i.i.d. law
-- statement:
--   Let Assumption 1 hold, $\gamma^{(0)}\in\Gamma^{(0)}$, $s\ge1$, and let $F\ge0$ be any function of the data $(\boldsymbol D_l(\hat s))_{l,\hat s}$ of cycle $s$. Let $A_s$ be the event that the exploration phase of cycle $s$ concludes within the first $IT$ periods. Then, under BidAlloc with any schedule,
--
--   $$
--   \mathbb E\bigl[\mathbb 1_{A_s}F\bigl((\boldsymbol D_l(\hat s))_{l,\hat s}\bigr)\bigr]\le\mathbb E_{\mathrm{iid}}\bigl[F\bigr],
--   $$
--
--   where $\mathbb E_{\mathrm{iid}}$ is the expectation of Lemma 3. This makes precise the sentence on p.17 that the observations correspond to placing the exploration bids repeatedly $s$ times, and licenses the application of Lemma 3 to data collected along the run.
--
--   Differences from the source:
--   - reading: "these observations correspond to the placing of the exploration bids … repeatedly $s$ times" → the expectation of any $F\ge0$ of the data on the event that the phase concludes is at most its i.i.d. expectation; reason: the data are collected adaptively and the phase may not conclude within the horizon, so a domination is the exact content used on p.20
--   - encoding: the expectation over random histories → a finite sum over outcome paths `ω : Fin (I * T) → Outcome L` weighted by `pathProb`, seasons 0-based; reason: a period has finitely many outcomes; no instance changes
--   - encoding: "there exist $k_l\in\mathbb N$ and a vector of exploration bids" (Assumption 2, p.12), the input of the policy (p.17) → the bids are the parameter `X : Exploration M`, with $k_l\ge 1$; reason: $\bar b_l$ is an input on p.17, and the phase needs a bid to place
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, p.17, "Note that these observations correspond to"; p.20, step $=(K_1)^{2T}Ls\,\mathbb E[\|\hat\gamma(s)-\gamma^{(0)}\|^2]$

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_phaseGap

set_option autoImplicit false

namespace MobilePromo

open Classical in
/-- The law of the exploration data (SSRN 3523491, p.17, "these observations correspond to the placing of
the exploration bids", used at the step `= (K₁)^{2T} L s E[‖γ̂(s) - γ⁽⁰⁾‖²]`, p.20): for every nonnegative
function `F` of the data of cycle `s`, the expectation under `BidAlloc` of `F` on the event that the
exploration phase of cycle `s` concludes within the horizon is at most its expectation under the
i.i.d. law of Lemma 3.

**Formalization Note** The page does not state this; Lemma 3 is applied there to adaptively collected
data, and this is what licenses that step. The inequality, rather than equality, is because the event may
fail. -/
theorem exploration_data_law (M : Model) (h1 : Assumption1 M) (X : Exploration M)
    (mle : MLESelector M X) {T : ℕ} (S : Schedule T) (I s : ℕ) (hs : 1 ≤ s) (γ₀ : M.ParamVec)
    (hγ₀ : γ₀ ∈ M.Gamma0) (F : ((l : Fin M.L) → Fin s → Fin (X.k l) → Bool) → ℝ)
    (hF : ∀ D, 0 ≤ F D) :
    pathExp M (bidAlloc M X mle S) γ₀ (I * T)
        (fun ω =>
          if ExplorationDone (phaseOf X.k (activeB S) (List.ofFn ω)) s then
            F ((phaseOf X.k (activeB S) (List.ofFn ω)).data X.k s)
          else 0) ≤
      iidExp M X γ₀ s F := by sorry

end MobilePromo
