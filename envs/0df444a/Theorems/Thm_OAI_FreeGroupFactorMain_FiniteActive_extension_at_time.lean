-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_extension_at_time
-- name    : OAI.FreeGroupFactorMain.FiniteActive.extension_at_time
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:01:35.819921+00:00
-- url     : https://prove2.me/theorems/e8be8782-4d15-4f25-87a4-ba88cccaac36
-- title:
--   Flow extension with inactive free generators
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be finite, $\kappa$ arbitrary, and let $M=L(\mathbb F(\iota\sqcup\kappa\sqcup\{*\}))$ with $c=\lambda(*)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, let $h_i$ ($i\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$, and let $X:\mathbb R\to U(M)^\iota$ solve $\dot X_i=i\bigl(\sum_g h_i(g)X_gSX_g^*\bigr)X_i$ with $X_i(0)=\lambda(i)$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. Let $T(t)$ be the tuple consisting of $X_i(t)$ on $\iota$ and $\lambda(k)$ on $\kappa$. For every $t$ there is a $\tau$-preserving ultraweakly continuous $*$-automorphism $\Phi$ of $M$ such that $\Phi(\lambda(g))$ is the evaluation of $g$ in $(T(t),c)$, for every word $g$.
--
--   Together with moment preservation, this extends the flow automorphisms of the paper to infinitely many inactive generators.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FiniteActive.extension_at_time`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteActive.lean#L96

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

theorem extension_at_time {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t : ℝ) :
    ∃ Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
            (generatorUnitary none)) g := by
  sorry

end FreeGroupFactorMain.FiniteActive
end
end OAI
