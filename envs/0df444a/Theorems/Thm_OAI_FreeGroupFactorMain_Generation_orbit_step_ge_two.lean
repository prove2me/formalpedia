-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Generation_orbit_step_ge_two
-- name    : OAI.FreeGroupFactorMain.Generation.orbit_step_ge_two
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:10.735324+00:00
-- url     : https://prove2.me/theorems/aa3716ef-0bb5-464c-ba65-d79195436c0d
-- title:
--   One orbit step toward a transported tuple, rank at least two
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\{*\}))$, and let the orbit be the set of tuples $(\Phi(\lambda(j)))_{j\in\mathrm{Fin}\,n}$ as $\Phi$ runs over the $\tau$-preserving $*$-automorphisms of $M$. For a tuple $V$ of unitaries, $V_g$ is the evaluation of the word $g$ and $\mathrm{poly}(V,p)=\sum_g p(g)V_g$. Tuples carry the metric $\mathrm{dist}(V,U)=\max_j\|V_j-U_j\|$ in the operator norm. Let $x_j$ be the free generators of $\mathbb F_n$. Let $n\ge2$, let $\Phi$ be a $\tau$-preserving $*$-automorphism of $M$, and $\theta>0$. There are $V$ in the orbit with $\mathrm{dist}\bigl(V,(\Phi(\lambda(j)))_j\bigr)<\theta$ and a word $w\in\mathbb F_n$ such that
--
--   $$\|V_{x_j}-\Phi(\lambda(j))\|_2<\theta\quad(j\in\mathrm{Fin}\,n),\qquad \|V_w-\Phi(\lambda(*))\|_2<\theta.$$
--
--   Thus, after a small move in the orbit, a word in the $n$-tuple approximates the transported extra generator.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Generation.orbit_step_ge_two`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteRank.lean#L57

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

theorem orbit_step_ge_two (n : ℕ) (hn : 2 ≤ n)
    (Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) {θ : ℝ} (hθ : 0 < θ) :
    ∃ V ∈ orbit n, dist V (mapTuple Φ (initial n)) < θ ∧
      ∃ w : FreeGroup (Fin n), ∀ j : Option (Fin n),
        twoNorm ((wordTuple V (fun j => j.elim w FreeGroup.of) j : Ambient n) -
          (mapTuple Φ generatorUnitary j : Ambient n)) < θ := by
  sorry

end Generation
end
end FreeGroupFactorMain
end OAI
