-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_displacement
-- name    : OAI.FreeGroupFactorMain.FiniteActive.displacement
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:05:52.584823+00:00
-- url     : https://prove2.me/theorems/1eb15c07-fb9a-4e73-a02a-e32f63c63108
-- title:
--   Displacement bounds with inactive free generators
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be finite, $\kappa$ arbitrary, $M=L(\mathbb F(\iota\sqcup\kappa\sqcup\{*\}))$, $c=\lambda(*)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $l(0)=0$, $S=\sum_kl(k)c^k$ self-adjoint and $\|S\|\le K$, and let $h_i$ be finitely supported real functions on $\mathbb F(\iota)$ with associated cocycle $D$, that is $D_{x_i}=h_i$ and $D_{gb}=D_g+\lambda(g)D_b$. There is a $\tau$-preserving ultraweakly continuous $*$-automorphism $\beta$ of $M$ fixing $c$ and every $\lambda(k)$, $k\in\kappa$, with
--
--   $$\|\beta(\lambda(i))-\lambda(i)\|\le3K\|h_i\|_{\ell^2},\qquad\|\beta(\lambda(w))-e^{iS}\lambda(w)\|\le3K\|D_w-\delta_e\|_{\ell^2}$$
--
--   for $i\in\iota$, $w\in\mathbb F(\iota)$. This is the paper's Proposition 3.1 with inactive generators.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FiniteActive.displacement`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteActive.lean#L281

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
open scoped ENNReal

end
open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem displacement (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K) :
    ∃ β : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
        (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ k : κ, β (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      (∀ i : ι, ‖β (groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))) -
        groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))‖ ≤
          3*K*Real.sqrt ((h i).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) *
          groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)‖ ≤
            3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  sorry

end
end FreeGroupFactorMain.FiniteActive
end
end OAI
