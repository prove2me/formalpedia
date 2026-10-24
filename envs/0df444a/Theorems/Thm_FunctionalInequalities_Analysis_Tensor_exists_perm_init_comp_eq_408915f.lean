-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_perm_init_comp_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:24.362998+00:00
-- url     : https://prove2.me/theorems/a1f9eada-6718-44ac-8f06-3e06c476c47a
-- title:
--   Permutation of Entries After Removing One Index
-- statement:
--   This statement describes the first $d$ entries of a permuted $(d+1)$-tuple.
--
--   Let $\alpha$ be a type, let $h:\operatorname{Fin}(d+1)\to\alpha$, let $\sigma$ be a permutation of $\operatorname{Fin}(d+1)$, and let $k\in\operatorname{Fin}(d+1)$. If
--
--   $$
--   \sigma(\operatorname{last}(d))=k,
--   $$
--
--   then there exists a permutation $\tau$ of $\operatorname{Fin}(d)$ such that
--
--   $$
--   \operatorname{init}(h\circ\sigma)=\operatorname{removeNth}(k,h)\circ\tau.
--   $$
--
--   Thus, after the entry indexed by $k$ is removed, the remaining entries agree up to permutation. This technical lemma supports reorganizing symmetrized multilinear expressions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L134-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_408915f {α : Type*} {d : ℕ} (h : Fin (d + 1) → α)
    (σ : Equiv.Perm (Fin (d + 1))) {k : Fin (d + 1)} (hk : σ (Fin.last d) = k) :
    ∃ τ : Equiv.Perm (Fin d), Fin.init (h ∘ σ) = k.removeNth h ∘ τ := by sorry
