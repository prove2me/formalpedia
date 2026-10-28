-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_filter_eq_two_mul_sum_filter_of_compl_invariant_readable
-- name    : FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:04.750635+00:00
-- url     : https://prove2.me/theorems/df0e8f70-61ce-476e-a922-0def8bd9c052
-- title:
--   Complement Pairing of Boolean Mask Sums
-- statement:
--   This is a finite-sum pairing identity for Boolean masks.
--
--   Let $P$ be a predicate on masks $q:\operatorname{Fin}(m)\to\{\mathrm{false},\mathrm{true}\}$, assume $P(q)$ is equivalent to $P(\neg q)$, and let $f$ assign a real number to each mask with $f(\neg q)=f(q)$. For any fixed $i_0\in\operatorname{Fin}(m)$,
--
--   $$\sum_{q:\,P(q)}f(q)=2\sum_{q:\,q(i_0)=\mathrm{true}\ \wedge\ P(q)}f(q).$$
--
--   The identity pairs every mask with its complement and is used to restrict symmetric subset sums to representatives containing a chosen slot.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_filter_eq_two_mul_sum_filter_of_compl_invariant {m : ℕ} (P : (Fin m → Bool) → Prop)
--       [DecidablePred P] (hP : ∀ q, P (fun i => !(q i)) ↔ P q) (f : (Fin m → Bool) → ℝ)
--       (hf : ∀ q, f (fun i => !(q i)) = f q) (i₀ : Fin m) :
--       ∑ q ∈ Finset.univ.filter P, f q = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Previous: [`directional_bilinear`](https://prove2.me/theorems/c7268247-0081-4a71-b098-d28d94f91226) · Next: [`selected_mask_partition`](https://prove2.me/theorems/cf1a6d5b-9b6d-481c-ae20-5dfef1453e3e).
--
--   [Source excerpt, lines 119–122](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L119-L122) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L116-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear

theorem FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant_readable {m : ℕ} (P : (Fin m → Bool) → Prop)
    [DecidablePred P] (hP : ∀ q, P (fun i => !(q i)) ↔ P q) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ q, f (fun i => !(q i)) = f q) (i₀ : Fin m) :
    ∑ q ∈ Finset.univ.filter P, f q = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by sorry
