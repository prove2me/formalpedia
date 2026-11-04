-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_laurent_flow_automorphisms
-- name    : OAI.FreeGroupFactorMain.laurent_flow_automorphisms
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T02:55:01.667001+00:00
-- url     : https://prove2.me/theorems/5bdfea58-dc7f-40b7-918a-6f9f089c0501
-- title:
--   Laurent flow times are trace-preserving automorphisms
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\iota$ be a finite type and $\Gamma=\mathbb F(\iota\sqcup\{*\})$ the free group on $\iota$ and one extra generator $*$; write $c=\lambda(*)$ in $L(\Gamma)$. Let $l:\mathbb Z\to\mathbb C$ be finitely supported with $S=\sum_k l(k)c^k$ self-adjoint, and let $h_j$ ($j\in\iota$) be finitely supported real functions on $\mathbb F(\iota)$. The flow of the paper is the differential equation $\dot X_j=i\Bigl(\sum_g h_j(g)X_gSX_g^*\Bigr)X_j$, where $X_g$ is the evaluation of the word $g$ in the tuple $X$. The flow has a solution $X$ with $X_j(0)=\lambda(j)$, and for every $t\in\mathbb R$ there is a $*$-automorphism $\Phi_t$ of $L(\Gamma)$ that preserves $\tau$, is ultraweakly continuous, and satisfies
--
--   $$\Phi_t(\lambda(g))=(X(t),c)_g\qquad(g\in\Gamma).$$
--
--   This is part of the flow construction in Section 3 of the paper, which turns the polynomial flow into trace-preserving automorphisms.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.laurent_flow_automorphisms`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Reducing.lean#L180

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end UnitaryEvaluation

open UnitaryEvaluation
open scoped ENNReal

open UnitaryEvaluation

theorem laurent_flow_automorphisms {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option ι)) l)) :
    ∃ (X : ℝ → ι → groupVonNeumann (FreeGroup (Option ι)))
      (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option ι)))),
      X 0 = (fun j => groupUnitary (FreeGroup.of (some j))) ∧
      (∀ t, HasDerivAt X (PolynomialFlow.field
        (laurentValue (generatorUnitary (none : Option ι)) l) h (X t)) t) ∧
      ∀ t, ∃ Φ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ]
          groupVonNeumann (FreeGroup (Option ι)),
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
          (groupUltraweakTopology (FreeGroup (Option ι))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨X t j, hU t j⟩) (generatorUnitary none)) g := by
  sorry

end
end FreeGroupFactorMain
end OAI
