-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m10
-- name    : NahmiasPerishable.Inventory.m10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:55.840482+00:00
-- url     : https://prove2.me/theorems/54900cbc-0073-4da1-b116-3c8133dd09ab
-- title:
--   Cohen augmented stock-decrease process
-- statement:
--   Define Aₙ as the total decrease in on hand stock in period n due to the combined effects of demand and outdating. Cohen shows that the vector valued stochastic process Yₙ = (Aₙ₋ₘ₊₁, ⋯, Aₙ₋₁) forms a positive recurrent discrete time continuous state Markov chain.
--
--   Differences from the source:
--   - encoding: lifetime m and n remaining periods → k = m−1 age coordinates and objective index n−1; reason: the recursion value n has n periods and objective j chooses the first order for j+1 periods
--   - reading: positive recurrent continuous-state Markov chain → an invariant probability with finite stationary conditional mean return time to every positive-mass measurable set; reason: this is the stationary return-time convention for positive recurrence; irreducibility and a single recurrent class are not printed and are not required
--   - encoding: the vector of the previous m−1 actual stock decreases → lagVector from an arbitrary canonical initial FIFO state, and the shift/max update verified in the conclusion; reason: lag histories are observed once m−1 periods exist, not replaced by arbitrary unrelated random variables
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §1.2.b(ii), Cohen augmented stock-decrease process (unnumbered), p. 689 (PDF 10), DOI:10.1287/opre.30.4.680; review attribution: Cohen [1976].

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

namespace NahmiasPerishable.Inventory

theorem m10 (D : Demand) (k : ℕ) (hk : 1 ≤ k) (S : ℝ) (hS : 0 ≤ S)
    (x : AgeState k) (hx : canonical true x) :
    (∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → ∀ t,
      lagVector k S x d (t+1) = lagStep k S (lagVector k S x d t) (d (t+k))) ∧
    Measurable (fun ad : (Fin k → ℝ) × ℝ => lagStep k S ad.1 ad.2) ∧
    MarkovFromShocks D.law (fun d t => lagVector k S x d t) (lagStep k S) ∧
    PositiveRecurrent D (lagStep k S) {a | ∀ i, 0 ≤ a i} := by sorry

end NahmiasPerishable.Inventory
