-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_lemmaA3_equilibrium_pairs
-- name    : GDPRPrivacy.PriceRise.lemmaA3_equilibrium_pairs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:18.710821+00:00
-- url     : https://prove2.me/theorems/6f624b45-3b01-4df4-b779-00ea1e8a8a21
-- title:
--   Lemma A3, pp. 33–34 — the three pairs of equilibria (1a, 2a), (1b, 2a), (1b, 2b)
-- statement:
--   Let $0 < x < 1$ and $\alpha \ge 0$. The pre-GDPR profit $\widehat\Pi$ and the post-GDPR profit $\widetilde\Pi$ each have a global maximizer over $\mathbb{R}$, and any two such maximizers $\hat p^\star$ (before) and $\tilde p^\star$ (after) satisfy:
--
--   1. if $x \le 1/2$ and $\alpha < \alpha_1(x)$, then $x < \hat p^\star < 1 + x$ (case 1a) and $x < \tilde p^\star < 1 + x$ (case 2a);
--   2. if $x \le 2 - \sqrt 2$ and $\alpha_1(x) \le \alpha < \alpha_2(x)$, then $x - 1 \le \hat p^\star \le x$ (case 1b) and $x < \tilde p^\star < 1 + x$ (case 2a);
--   3. if $x \le 1$ and $\alpha \ge \alpha_2(x)$, then $x - 1 \le \hat p^\star \le x$ (case 1b) and $0 \le \tilde p^\star \le x$ (case 2b).
--
--   Here $\alpha_1(x) = \max\{(1-2x)/2, 0\}$ and $\alpha_2(x) = \max\{(2-4x+x^2)/(2x), 0\}$. The lemma sorts every parameter pair $(x, \alpha)$ into one of three regions according to which demand regime is active at the equilibrium price before and after the GDPR; every comparison of equilibria in the paper is made region by region.
--
--   **Formalization Note** "Case 1a/1b/2a/2b equilibrium" is encoded as membership of the maximizer in the case's price interval (pp. 10, 13). The bullets keep their printed side conditions $x \le 1/2$, $x \le 2 - \sqrt 2$, $x \le 1$, even where they are implied. The existence conjuncts make the statement about "any two maximizers" non-vacuous.
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), pp. 33–34, Lemma A3

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem lemmaA3_equilibrium_pairs (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) :
    (∃ p, IsMaxOn (profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde : ℝ,
      IsMaxOn (profitBefore x α) Set.univ pHat →
      IsMaxOn (profitAfter x α) Set.univ pTilde →
        (x ≤ 1 / 2 → α < alpha1 x →
          (x < pHat ∧ pHat < 1 + x) ∧ (x < pTilde ∧ pTilde < 1 + x)) ∧
        (x ≤ 2 - Real.sqrt 2 → alpha1 x ≤ α → α < alpha2 x →
          (x - 1 ≤ pHat ∧ pHat ≤ x) ∧ (x < pTilde ∧ pTilde < 1 + x)) ∧
        (x ≤ 1 → alpha2 x ≤ α →
          (x - 1 ≤ pHat ∧ pHat ≤ x) ∧ (0 ≤ pTilde ∧ pTilde ≤ x)) := by sorry

end GDPRPrivacy.PriceRise
