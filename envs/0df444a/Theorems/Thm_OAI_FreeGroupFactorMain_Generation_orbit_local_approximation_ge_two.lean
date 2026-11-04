-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Generation_orbit_local_approximation_ge_two
-- name    : OAI.FreeGroupFactorMain.Generation.orbit_local_approximation_ge_two
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:59:35.490125+00:00
-- url     : https://prove2.me/theorems/5b9c9709-ddd7-4513-befc-7ba214e19e8e
-- title:
--   Local approximation inside the orbit, rank at least two
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$, and let the orbit be the set of tuples $(\Phi(\lambda(j)))_{j\in\mathrm{Fin}\,n}$ as $\Phi$ runs over the $\tau$-preserving $*$-automorphisms of $M$. For a tuple $V$ of unitaries, $V_g$ is the evaluation of the word $g$ and $\mathrm{poly}(V,p)=\sum_g p(g)V_g$. Tuples carry the metric $\mathrm{dist}(V,U)=\max_j\|V_j-U_j\|$ in the operator norm. Let $n\ge2$. For every $U$ in the orbit, every $\delta,\varepsilon>0$ and every $g\in\mathbb F(\mathrm{Fin}\,n\sqcup\{*\})$ there are $V$ in the orbit with $\mathrm{dist}(V,U)<\delta$ and a finitely supported $p:\mathbb F_n\to\mathbb C$ such that
--
--   $$\|\mathrm{poly}(V,p)-\lambda(g)\|_2<\varepsilon.$$
--
--   The paper's Section 5 iteration treats $n\ge3$; this is the rank-at-least-two version of the Lean counterpart of its inductive step: a small move within the orbit brings a word algebra of the tuple close to any prescribed basis vector. In Lean it feeds a Baire-type lemma rather than an explicit iteration.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Generation.orbit_local_approximation_ge_two`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteRank.lean#L91

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

theorem orbit_local_approximation_ge_two (n : ℕ) (hn : 2 ≤ n)
    (U : Tuple n) (hU : U ∈ orbit n) (δ : ℝ) (hδ : 0 < δ)
    (g : FreeGroup (Option (Fin n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit n, dist V U < δ ∧ ∃ p : FreeGroup (Fin n) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  sorry

end Generation
end
end FreeGroupFactorMain
end OAI
