-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_laurent_flow_displacement
-- name    : OAI.FreeGroupFactorMain.laurent_flow_displacement
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:08:05.496693+00:00
-- url     : https://prove2.me/theorems/414debff-bf35-45e6-b3a8-3edb6d8020ed
-- title:
--   Displacement bounds for the time-one Laurent flow
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be a finite type and $\Gamma=\mathbb F(\iota\sqcup\{*\})$ the free group on $\iota$ and one extra generator $*$; write $c=\lambda(*)$ in $L(\Gamma)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, and let $h_j$ ($j\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$. The flow is the differential equation $\dot X_j=i\Bigl(\sum_g h_j(g)X_gSX_g^*\Bigr)X_j$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. Assume $l(0)=0$ and $\|S\|\le K$. Let $D$ be the free-group cocycle with $D_{x_j}=h_j$ and $D_{gb}=D_g+\lambda(g)D_b$. There is a $\tau$-preserving, ultraweakly continuous $*$-automorphism $\beta$ of $L(\Gamma)$ fixing $c$ such that
--
--   $$\|\beta(\lambda(j))-\lambda(j)\|\le 3K\|h_j\|_{\ell^2},\qquad \|\beta(\lambda(w))-e^{iS}\lambda(w)\|\le 3K\|D_w-\delta_e\|_{\ell^2}$$
--
--   for all $j\in\iota$ and $w\in\mathbb F(\iota)$. These are the displacement estimates of Proposition 3.1 of the paper, with a Laurent polynomial $S$ in place of the bounded logarithm of $c$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.laurent_flow_displacement`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Cocycles.lean#L403

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem laurent_flow_displacement
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l))
    (K : ℝ) (hK : 0 ≤ K) (hn : ‖laurentValue (generatorUnitary (none : Option ι)) l‖ ≤ K) :
    ∃ β : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ j : ι, ‖β (groupUnitary (FreeGroup.of (some j))) - groupUnitary (FreeGroup.of (some j))‖ ≤
        3*K*Real.sqrt ((h j).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map Option.some w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option ι)) l) *
          groupUnitary (FreeGroup.map Option.some w)‖ ≤
        3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  sorry

end
end
end FreeGroupFactorMain
end OAI
