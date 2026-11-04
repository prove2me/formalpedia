-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_InfiniteGeneration_generating_tuple
-- name    : OAI.FreeGroupFactorMain.InfiniteGeneration.generating_tuple
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:55:26.149371+00:00
-- url     : https://prove2.me/theorems/79e10dba-8910-439e-800e-75f9205695e6
-- title:
--   A freely generating Haar triple of the infinite-rank factor
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\mathrm{Index}=\mathrm{Fin}\,3\sqcup\mathbb N\sqcup\{*\}$ and $M=L(\mathbb F(\mathrm{Index}))$. Let $A_i=\lambda(i)$ for $i\in\mathrm{Fin}\,3$ be the initial tuple, and for $q\in\mathbb N\sqcup\{*\}$ let $E_q=\lambda(q)$ be the extra generators. The orbit is the set of tuples $(\Phi(A_i))_i$ for $\tau$-preserving $*$-automorphisms $\Phi$ of $M$. There is a triple $U$ of unitaries in $M$ with $\tau(U_g)=0$ for every nonidentity $g\in\mathbb F_3$ and
--
--   $$\overline{\mathrm{span}}\{U_g\delta_e:g\in\mathbb F_3\}=\ell^2(\mathbb F(\mathrm{Index})).$$
--
--   With Lemma 2.2 of the paper this gives the identification $L(\mathbb F_3)\cong L(\mathbb F_\infty)$ used for the infinite parameter.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.InfiniteGeneration.generating_tuple`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Main.lean#L28

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain

namespace InfiniteGeneration

theorem generating_tuple :
    ∃ U : Tuple,
      (∀ g : FreeGroup (Fin 3), canonicalTrace (Generation.word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (Generation.word U g)))).topologicalClosure := by
  sorry

end InfiniteGeneration
end FreeGroupFactorMain
end
end OAI
