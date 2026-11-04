-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_InfiniteGeneration_generating_haar_tuple
-- name    : OAI.FreeGroupFactorMain.InfiniteGeneration.generating_haar_tuple
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:13.293493+00:00
-- url     : https://prove2.me/theorems/552a91d9-3c23-45c9-af2b-b78a62d2bd7d
-- title:
--   Limit tuple at infinite rank from local approximation
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\mathrm{Index}=\mathrm{Fin}\,3\sqcup\mathbb N\sqcup\{*\}$ and $M=L(\mathbb F(\mathrm{Index}))$. Let $A_i=\lambda(i)$ for $i\in\mathrm{Fin}\,3$ be the initial tuple, and for $q\in\mathbb N\sqcup\{*\}$ let $E_q=\lambda(q)$ be the extra generators. The orbit is the set of tuples $(\Phi(A_i))_i$ for $\tau$-preserving $*$-automorphisms $\Phi$ of $M$. Tuples carry the metric $\mathrm{dist}(V,U)=\max_i\|V_i-U_i\|$ in the operator norm. Assume that for every $U$ in the orbit, $\delta,\varepsilon>0$ and $g\in\mathbb F(\mathrm{Index})$ there are $V$ in the orbit with $\mathrm{dist}(V,U)<\delta$ and a finitely supported $p$ on $\mathbb F_3$ with $\|\sum_hp(h)V_h-\lambda(g)\|_2<\varepsilon$. Then there is a triple $U$ of unitaries in $M$ with $\tau(U_g)=0$ for every nonidentity $g\in\mathbb F_3$ and
--
--   $$\overline{\mathrm{span}}\{U_g\delta_e:g\in\mathbb F_3\}=\ell^2(\mathbb F(\mathrm{Index})).$$
--
--   This is the limit step for the infinite-rank factor. Lean proves it by a Baire-type lemma rather than by the explicit iteration of Section 5 of the paper, which treats finite rank.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.InfiniteGeneration.generating_haar_tuple`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/InfiniteGeneration.lean#L431

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

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

theorem generating_haar_tuple
    (hlocal : ∀ U ∈ orbit, ∀ δ : ℝ, 0 < δ → ∀ g : Group, ∀ ε : ℝ, 0 < ε →
      ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
        dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε) :
    ∃ U : Tuple,
      (∀ g : FreeGroup (Fin 3), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  sorry

end FreeGroupFactorMain.InfiniteGeneration
end
end OAI
