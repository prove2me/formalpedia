-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_selected_eq_readable
-- name    : FunctionalInequalities.KLS.BKL.sum_selected_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:19.759375+00:00
-- url     : https://prove2.me/theorems/fa7bea17-a11a-4926-a7d5-5e7c584f47ec
-- title:
--   Reindexing a Mask-Selected Finite Sum
-- statement:
--   This reindexes a sum over Boolean masks by the selected and complementary slots.
--
--   Let $w:\iota\to E$, let $q:\operatorname{Fin}(k)\to\{\mathrm{false},\mathrm{true}\}$, and let $G$ map pairs of lists in $E$ to $\mathbb{R}$. If the mask has $c_1$ true entries and its complement has $c_2$ true entries, then
--
--   $$
--   \sum_{J:\operatorname{Fin}(k)\to\iota}
--   G\bigl(w(J)\text{ selected by }q,\,w(J)\text{ selected by }\neg q\bigr)
--   =
--   \sum_{J_1:\operatorname{Fin}(c_1)\to\iota}
--   \sum_{J_2:\operatorname{Fin}(c_2)\to\iota}
--   G\bigl(w(J_1),w(J_2)\bigr).
--   $$
--
--   The formal functions `maskCount` and `selected` specify the two lists and their lengths. This is a combinatorial reindexing tool for cumulant-energy decompositions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_selected_eq {E ι : Type*} [Fintype ι] (w : ι → E) :
--       ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
--         maskCount q = c₁ → maskCount (fun i => !(q i)) = c₂ →
--         ∑ J : Fin k → ι, G (selected (fun i => w (J i)) q)
--             (selected (fun i => w (J i)) (fun i => !(q i))) =
--           ∑ J₁ : Fin c₁ → ι, ∑ J₂ : Fin c₂ → ι,
--             G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086).
--
--   Definition modules: [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Next: [`sqrt_sum_sq_sum_le`](https://prove2.me/theorems/f159c409-0b24-4a71-8718-4a4409e0445e).
--
--   [Source excerpt, lines 169–175](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L169-L175) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L168-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sum_selected_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

theorem FunctionalInequalities.KLS.BKL.sum_selected_eq_readable {E ι : Type*} [Fintype ι] (w : ι → E) :
    ∀ (k : ℕ) (q : Fin k → Bool) (G : List E → List E → ℝ) (c₁ c₂ : ℕ),
      maskCount q = c₁ → maskCount (fun i => !(q i)) = c₂ →
      ∑ J : Fin k → ι, G (selected (fun i => w (J i)) q)
          (selected (fun i => w (J i)) (fun i => !(q i))) =
        ∑ J₁ : Fin c₁ → ι, ∑ J₂ : Fin c₂ → ι,
          G (List.ofFn fun i => w (J₁ i)) (List.ofFn fun i => w (J₂ i)) := by sorry
