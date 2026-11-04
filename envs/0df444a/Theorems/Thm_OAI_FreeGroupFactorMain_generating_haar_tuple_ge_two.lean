-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_generating_haar_tuple_ge_two
-- name    : OAI.FreeGroupFactorMain.generating_haar_tuple_ge_two
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:56:44.114418+00:00
-- url     : https://prove2.me/theorems/0cc37641-1510-41fa-a385-591d2a94be74
-- title:
--   Freely generating Haar tuple of rank n in L(F_{n+1}), n at least two
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $n\ge2$ and $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$. There is an $n$-tuple $U$ of unitaries in $M$ with $\tau(U_g)=0$ for every nonidentity $g\in\mathbb F_n$, and such that the vectors $U_g\delta_e$ have dense linear span in $\ell^2(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$:
--
--   $$\overline{\mathrm{span}}\{U_g\delta_e:g\in\mathbb F_n\}=\ell^2.$$
--
--   The proof of Theorem 1.1 of the paper treats $n\ge3$; this statement also covers rank two, and Lean obtains the tuple by a Baire-type lemma rather than an explicit iteration.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.generating_haar_tuple_ge_two`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteRank.lean#L122

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

open UnitaryEvaluation

namespace Generation

end Generation

open Generation

theorem generating_haar_tuple_ge_two (n : ℕ) (hn : 2 ≤ n) :
    ∃ U : Tuple n,
      (∀ g : FreeGroup (Fin n), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  sorry

end
end FreeGroupFactorMain
end OAI
