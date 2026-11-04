-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_gauged_nielsen_iso
-- name    : OAI.FreeGroupFactorMain.gauged_nielsen_iso
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:01:38.642632+00:00
-- url     : https://prove2.me/theorems/03fedd8e-2458-43e0-80f8-cb9036fefbbb
-- title:
--   Gauged Nielsen automorphism fixing the first generators
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $\Gamma=\mathbb F(\iota\sqcup\{*\})$, $w\in\mathbb F(\iota)$ and let $z$ be a complex number of modulus one. There is a $*$-automorphism $\gamma$ of $L(\Gamma)$ which preserves $\tau$, is ultraweakly continuous with ultraweakly continuous inverse, fixes $\lambda(j)$ for $j\in\iota$, and satisfies
--
--   $$\gamma(\lambda(*))=z\,\lambda(*)\lambda(w).$$
--
--   This is the free-group basis change used in the proof of Proposition 5.1 of the paper, combined with a scalar phase.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.gauged_nielsen_iso`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/Nielsen.lean#L162

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

variable {ι : Type uι}

theorem gauged_nielsen_iso (w : FreeGroup ι) (z : unitary ℂ) :
    ∃ γ : groupVonNeumann (FreeGroup (Option ι)) ≃⋆ₐ[ℂ] groupVonNeumann (FreeGroup (Option ι)),
      (∀ T, canonicalTrace (γ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option ι)))
        (groupUltraweakTopology (FreeGroup (Option ι))) γ.symm ∧
      (∀ j, γ (groupUnitary (FreeGroup.of (some j))) = groupUnitary (FreeGroup.of (some j))) ∧
      γ (groupUnitary (FreeGroup.of none)) =
        (z : ℂ) • (groupUnitary (FreeGroup.of none) * groupUnitary (FreeGroup.map Option.some w)) := by
  sorry

end FreeGroupFactorMain
end
end OAI
