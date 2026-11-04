-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_moments
-- name    : OAI.FreeGroupFactorMain.FiniteActive.moments
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:13.243337+00:00
-- url     : https://prove2.me/theorems/2c308415-8926-4e11-9deb-b728d1a041dd
-- title:
--   Moment preservation with inactive free generators
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be finite, $\kappa$ arbitrary, and let $M=L(\mathbb F(\iota\sqcup\kappa\sqcup\{*\}))$ with $c=\lambda(*)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, let $h_i$ ($i\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$, and let $X:\mathbb R\to U(M)^\iota$ solve $\dot X_i=i\bigl(\sum_g h_i(g)X_gSX_g^*\bigr)X_i$ with $X_i(0)=\lambda(i)$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. Let $T(t)$ be the tuple consisting of $X_i(t)$ on $\iota$ and the original $\lambda(k)$ on $\kappa$. Then for all $t$ and all $g\in\mathbb F(\iota\sqcup\kappa\sqcup\{*\})$, the evaluation of $g$ in $(T(t),c)$ has trace $1$ if $g=e$ and $0$ otherwise.
--
--   This extends the moment invariance of the paper's Lemma 3.4 to an ambient free group with additional generators on which the flow does not act.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FiniteActive.moments`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteMoments.lean#L302

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

theorem moments [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue
      (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) :
    ∀ t (g : FreeGroup (Option (ι ⊕ κ))), canonicalTrace (wordHom
      (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
        (generatorUnitary none)) g) = if g = 1 then 1 else 0 := by
  sorry

end FreeGroupFactorMain.FiniteActive
end
end OAI
