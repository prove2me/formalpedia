-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_InfiniteGeneration_one_step_extra_of_none
-- name    : OAI.FreeGroupFactorMain.InfiniteGeneration.one_step_extra_of_none
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:56:50.551356+00:00
-- url     : https://prove2.me/theorems/576c926a-5121-435a-a238-8d6857c4a60a
-- title:
--   Absorbing any extra generator from the distinguished one
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\mathrm{Index}=\mathrm{Fin}\,3\sqcup\mathbb N\sqcup\{*\}$ and $M=L(\mathbb F(\mathrm{Index}))$. Let $A_i=\lambda(i)$ for $i\in\mathrm{Fin}\,3$ be the initial tuple, and for $q\in\mathbb N\sqcup\{*\}$ let $E_q=\lambda(q)$ be the extra generators. The orbit is the set of tuples $(\Phi(A_i))_i$ for $\tau$-preserving $*$-automorphisms $\Phi$ of $M$. Assume that for every $\varepsilon>0$ there are a $\tau$-preserving automorphism $\alpha$ fixing each $E_k$, $k\in\mathbb N$, and a word $w\in\mathbb F_3$ with $\|\alpha(A_i)-A_i\|<\varepsilon$ and $\|\alpha(A_w)-E_*\|_2<\varepsilon$. Then for every $q$ and $\varepsilon>0$ there are a $\tau$-preserving automorphism $\alpha$ fixing each $E_r$, $r\ne q$, and a word $w\in\mathbb F_3$ with
--
--   $$\|\alpha(A_i)-A_i\|<\varepsilon,\qquad\|\alpha(A_w)-E_q\|_2<\varepsilon.$$
--
--   This reduces the absorption of an arbitrary extra generator to the distinguished one.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.InfiniteGeneration.one_step_extra_of_none`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/InfiniteGeneration.lean#L128

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

theorem one_step_extra_of_none
    (hone : ∀ ε : ℝ, 0 < ε → ∃ α : M ≃⋆ₐ[ℂ] M,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : ℕ, α (extra (some k) : M) = (extra (some k) : M)) ∧
      ∃ w : FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        twoNorm (α (word initial w)-(extra none : M)) < ε)
    (q : Option ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : M ≃⋆ₐ[ℂ] M, (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ r : Option ℕ, r ≠ q → α (extra r : M) = (extra r : M)) ∧
      ∃ w : FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        twoNorm (α (word initial w)-(extra q : M)) < ε := by
  sorry

end FreeGroupFactorMain.InfiniteGeneration
end
end OAI
