-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_actual_laurent_flow_moments
-- name    : OAI.FreeGroupFactorMain.actual_laurent_flow_moments
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:08:04.403618+00:00
-- url     : https://prove2.me/theorems/5983148e-6ee4-4fbd-bf62-8ab1f34ce73a
-- title:
--   Moment preservation along the Laurent flow
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be a finite type and $\Gamma=\mathbb F(\iota\sqcup\{*\})$ the free group on $\iota$ and one extra generator $*$; write $c=\lambda(*)$ in $L(\Gamma)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, and let $h_j$ ($j\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$. The flow of the paper is the differential equation $\dot X_j=i\Bigl(\sum_g h_j(g)X_gSX_g^*\Bigr)X_j$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. The flow has a solution $X:\mathbb R\to U(L(\Gamma))^\iota$ with $X_j(0)=\lambda(j)$ such that the tuple $(X(t),c)$ has the same moments as the generators: for all $t\in\mathbb R$ and $g\in\Gamma$,
--
--   $$\tau\bigl((X(t),c)_g\bigr)=\begin{cases}1,&g=e,\\0,&g\ne e.\end{cases}$$
--
--   This is the moment invariance of the flow (Lemma 3.4 of the paper) in the Laurent-polynomial setting.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.actual_laurent_flow_moments`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/MomentFlow.lean#L203

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

theorem actual_laurent_flow_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (UnitaryEvaluation.laurentValue
      (generatorUnitary (none : Option ι)) l)) :
    ∃ (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
      (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι)))),
      X 0 = (fun j => groupUnitary (FreeGroup.of (some j))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (UnitaryEvaluation.laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) ∧
      ∀ t (g : FreeGroup (Option ι)),
        canonicalTrace (UnitaryEvaluation.wordHom
          (UnitaryEvaluation.extendUnitary (fun j => ⟨X t j, hU t j⟩)
            (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  sorry

end FreeGroupFactorMain
end
end OAI
