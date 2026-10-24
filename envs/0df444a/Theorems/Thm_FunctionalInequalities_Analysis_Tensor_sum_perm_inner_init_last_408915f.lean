-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_perm_inner_init_last_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:27.905991+00:00
-- url     : https://prove2.me/theorems/31913d1f-80b1-40a0-904c-9cfd8cd1bfcf
-- title:
--   Permutation Sum for a Symmetric Multilinear Map
-- statement:
--   This statement evaluates a permutation sum for a symmetric continuous multilinear map.
--
--   Let $E$ be a real inner-product space, let $d\in\mathbb N$, and let $\Phi:E^d\to E$ be a continuous $d$-linear map satisfying
--
--   $$
--   \Phi(v\circ\tau)=\Phi(v)
--   $$
--
--   for every permutation $\tau$ of $\operatorname{Fin}(d)$ and every $v:\operatorname{Fin}(d)\to E$. For $h:\operatorname{Fin}(d+1)\to E$, one has
--
--   $$
--   \sum_{\sigma\in\operatorname{Sym}(d+1)}
--   \left\langle
--   \Phi\bigl(\operatorname{init}(h\circ\sigma)\bigr),
--    h(\sigma(\operatorname{last}(d)))
--   \right\rangle
--   =(d!)\sum_{k\in\operatorname{Fin}(d+1)}
--   \left\langle
--   \Phi(\operatorname{removeNth}(k,h)),h(k)
--   \right\rangle.
--   $$
--
--   This is the counting identity underlying symmetrization of a multilinear map paired with one additional vector.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L164-L227 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_408915f {d : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E)
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (v : Fin d → E), Φ (v ∘ τ) = Φ v) (h : Fin (d + 1) → E) :
    ∑ σ : Equiv.Perm (Fin (d + 1)), ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫ =
      (d.factorial : ℝ) * ∑ k : Fin (d + 1), ⟪Φ (k.removeNth h), h k⟫ := by sorry
