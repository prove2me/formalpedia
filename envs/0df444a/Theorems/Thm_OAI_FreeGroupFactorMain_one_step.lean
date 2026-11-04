-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_one_step
-- name    : OAI.FreeGroupFactorMain.one_step
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:55:10.196593+00:00
-- url     : https://prove2.me/theorems/713f8283-4a49-42ee-8007-871739a1152b
-- title:
--   One-step approximation of the extra generator
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $n\ge3$, $\varepsilon>0$, $\Gamma=\mathbb F(\mathrm{Fin}\,n\sqcup\{*\})$. There are a $\tau$-preserving ultraweakly continuous $*$-automorphism $\alpha$ of $L(\Gamma)$ and a word $w\in\mathbb F_n$ such that
--
--   $$\|\alpha(\lambda(j))-\lambda(j)\|<\varepsilon\quad(j\in\mathrm{Fin}\,n),\qquad \|\alpha(\lambda(w))-\lambda(*)\|_2<\varepsilon.$$
--
--   This is the form used in Lean of Proposition 5.1 of the paper, with the second estimate in $\|\cdot\|_2$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.one_step`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/LocalAutomorphism.lean#L257

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

variable {G : Type uG} [Group G]

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

theorem one_step (n : ℕ) (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : groupVonNeumann (FreeGroup (Option (Fin n))) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option (Fin n))),
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (Fin n))))
        (groupUltraweakTopology (FreeGroup (Option (Fin n)))) α ∧
      ∃ w : FreeGroup (Fin n),
        (∀ j : Fin n, ‖α (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map Option.some w)) - groupUnitary (FreeGroup.of none)) < ε := by
  sorry

end FreeGroupFactorMain
end
end OAI
