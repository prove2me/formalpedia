-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Generation_orbit_local_approximation
-- name    : OAI.FreeGroupFactorMain.Generation.orbit_local_approximation
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:05.865539+00:00
-- url     : https://prove2.me/theorems/f79115f1-50ed-455a-a61a-97edd517c6d4
-- title:
--   Local approximation inside the orbit, rank at least three
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$, and let the orbit be the set of tuples $(\Phi(\lambda(j)))_{j\in\mathrm{Fin}\,n}$ as $\Phi$ runs over the $\tau$-preserving $*$-automorphisms of $M$. For a tuple $V$ of unitaries, $V_g$ is the evaluation of the word $g$ and $\mathrm{poly}(V,p)=\sum_g p(g)V_g$. Tuples carry the metric $\mathrm{dist}(V,U)=\max_j\|V_j-U_j\|$ in the operator norm. Let $n\ge3$. For every $U$ in the orbit, every $\delta,\varepsilon>0$ and every $g\in\mathbb F(\mathrm{Fin}\,n\sqcup\{*\})$ there are $V$ in the orbit with $\mathrm{dist}(V,U)<\delta$ and a finitely supported $p:\mathbb F_n\to\mathbb C$ such that
--
--   $$\|\mathrm{poly}(V,p)-\lambda(g)\|_2<\varepsilon.$$
--
--   This is the Lean counterpart of the inductive step of the iteration in Section 5 of the paper: a small move within the orbit brings a word algebra of the tuple close to any prescribed basis vector. In Lean it feeds a Baire-type lemma rather than an explicit iteration.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Generation.orbit_local_approximation`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Generation.lean#L178

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

end

theorem orbit_local_approximation (n : ℕ) (hn : 3 ≤ n)
    (U : Tuple n) (hU : U ∈ orbit n) (δ : ℝ) (hδ : 0 < δ)
    (g : FreeGroup (Option (Fin n))) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ orbit n, dist V U < δ ∧ ∃ p : FreeGroup (Fin n) →₀ ℂ,
      dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε := by
  sorry

end FreeGroupFactorMain.Generation
end
end OAI
