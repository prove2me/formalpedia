-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_apply_comp_cast_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:36.760972+00:00
-- url     : https://prove2.me/theorems/f3dc6e21-450b-4d16-aab4-8e4451661aaa
-- title:
--   Entrywise Formula for Partial Symmetrization
-- statement:
--   Let $N,q,r,n\in\mathbb N$ with $N=q+r$, let $A$ be an $N$-index coordinate tensor over an $n$-element coordinate space, and let $J:\mathrm{Fin}(N)\to\mathrm{Fin}(n)$. Then the entry of the symmetrization over the first $q$ positions is the average over permutations of those positions, while the last $r$ positions remain fixed:
--
--   $$S_qA(J)=\frac1{q!}\sum_{\tau\in\operatorname{Perm}(q)}
--   A\bigl(J\circ(\tau\text{ on the first }q\text{ slots})\,\text{ followed by }J\text{ on the last }r\text{ slots}\bigr).$$
--
--   The equality includes the necessary cast from the equality $N=q+r$ and is an entrywise coordinate identity. It is used to expand symmetrized Taylor fields.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetrize_apply_comp_cast {n N q r : ℕ} (h : N = q + r) (A : Coord n N)
--       (J : Fin (q + r) → Fin n) :
--       symmetrize n N q A (J ∘ Fin.cast h) =
--         (q.factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin q),
--           A (Fin.append (J ∘ Fin.castAdd r ∘ τ) (J ∘ Fin.natAdd q) ∘ Fin.cast h)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f).
--
--   Previous: [`taylorTensor_center`](https://prove2.me/theorems/2224e876-b11e-4fc6-980d-876a9062141d) · Next: [`taylorTensor_gen_apply`](https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1).
--
--   [Source excerpt, lines 201–205](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L201-L205) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L199-L216 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open FunctionalInequalities.Analysis.Tensor

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast_readable {n N q r : ℕ} (h : N = q + r) (A : Coord n N)
    (J : Fin (q + r) → Fin n) :
    symmetrize n N q A (J ∘ Fin.cast h) =
      (q.factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin q),
        A (Fin.append (J ∘ Fin.castAdd r ∘ τ) (J ∘ Fin.natAdd q) ∘ Fin.cast h) := by sorry
