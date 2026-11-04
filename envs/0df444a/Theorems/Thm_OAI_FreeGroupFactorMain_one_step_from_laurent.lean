-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_one_step_from_laurent
-- name    : OAI.FreeGroupFactorMain.one_step_from_laurent
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:08:06.632048+00:00
-- url     : https://prove2.me/theorems/de81674e-dbc3-403f-8c48-69c16caf5f0e
-- title:
--   One-step perturbation from Laurent and cocycle data
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $n\in\mathbb N$, $\varepsilon>0$, $\Gamma=\mathbb F(\mathrm{Fin}\,n\sqcup\{*\})$ and $c=\lambda(*)$. Suppose $l:\mathbb Z\to\mathbb C$ is finitely supported with $l(0)=0$, that $S=\sum_k l(k)c^k$ is self-adjoint with $\|S\|\le 2(\pi+1)$, and that $z$ is a scalar of modulus one with $\|e^{iS}-zc\|_2<\varepsilon/2$. Suppose $h$ is a finitely supported real function on $\mathbb F_n$ and $w\in\mathbb F_n$, and let $D$ be the free-group cocycle with $D_{x_1}=h$, $D_{x_j}=0$ for $j\ne1$, and $D_{gb}=D_g+\lambda(g)D_b$. If
--
--   $$\|h\|_{\ell^2}<\frac{\varepsilon/2}{6(\pi+1)},\qquad \|D_w-\delta_e\|_{\ell^2}<\frac{\varepsilon/2}{6(\pi+1)},$$
--
--   then there are a $\tau$-preserving ultraweakly continuous $*$-automorphism $\alpha$ of $L(\Gamma)$ and a word $w'\in\mathbb F_n$ with $\|\alpha(\lambda(j))-\lambda(j)\|<\varepsilon$ for all $j$ and $\|\alpha(\lambda(w'))-c\|_2<\varepsilon$.
--
--   This reduces the one-step statement of Proposition 5.1 of the paper to the coefficient problem.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.one_step_from_laurent`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/LocalAutomorphism.lean#L219

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

theorem one_step_from_laurent (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n))) l) - (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
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
