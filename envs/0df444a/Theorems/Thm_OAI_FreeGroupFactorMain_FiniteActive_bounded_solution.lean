-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_bounded_solution
-- name    : OAI.FreeGroupFactorMain.FiniteActive.bounded_solution
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:02:32.150931+00:00
-- url     : https://prove2.me/theorems/53510047-5635-47de-94f5-df91113ad583
-- title:
--   Uniform Hamiltonian bound along a flow solution
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be finite, $\kappa$ arbitrary, and let $M=L(\mathbb F(\iota\sqcup\kappa\sqcup\{*\}))$ with $c=\lambda(*)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, let $h_i$ ($i\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$, and let $X:\mathbb R\to U(M)^\iota$ solve $\dot X_i=i\bigl(\sum_g h_i(g)X_gSX_g^*\bigr)X_i$ with $X_i(0)=\lambda(i)$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. Assume $l(0)=0$ and $\|S\|\le K$. For every $t$ and every finitely supported real function $k$ on $\mathbb F(\iota)$,
--
--   $$\Bigl\|\sum_g k(g)X_g(t)SX_g(t)^*\Bigr\|\le 3K\|k\|_{\ell^2}.$$
--
--   This is the free-sum estimate of Lemma 2.5 of the paper along the flow; the bound does not depend on the support of $k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FiniteActive.bounded_solution`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteActive.lean#L195

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

theorem bounded_solution (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K)
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t k, ‖hamiltonianLinear
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l)
        (fun i => ⟨X t i,hU t i⟩) k‖ ≤ 3*K*Real.sqrt (k.sum (fun _ r => r^2)) := by
  sorry

end
end FreeGroupFactorMain.FiniteActive
end
end OAI
