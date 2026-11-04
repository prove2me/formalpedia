-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_one_step_from_laurent
-- name    : OAI.FreeGroupFactorMain.FiniteActive.one_step_from_laurent
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:08:05.473443+00:00
-- url     : https://prove2.me/theorems/999dedef-0dbd-4853-92ef-af4efe7a97ad
-- title:
--   One-step perturbation with inactive free generators
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $n\in\mathbb N$, $\kappa$ arbitrary, $\varepsilon>0$, $M=L(\mathbb F(\mathrm{Fin}\,n\sqcup\kappa\sqcup\{*\}))$, $c=\lambda(*)$. Suppose $l$ is finitely supported with $l(0)=0$, $S=\sum_kl(k)c^k$ is self-adjoint with $\|S\|\le2(\pi+1)$, and $\|e^{iS}-zc\|_2<\varepsilon/2$ for a scalar $z$ of modulus one. Suppose $h$ is a finitely supported real function on $\mathbb F_n$ and $w\in\mathbb F_n$ with $\|h\|_{\ell^2}$ and $\|D_w-\delta_e\|_{\ell^2}$ both below $\frac{\varepsilon/2}{6(\pi+1)}$, where $D$ is the cocycle with $D_{x_1}=h$, $D_{x_i}=0$ for $i\ne1$, and $D_{gb}=D_g+\lambda(g)D_b$. Then there are a $\tau$-preserving $*$-automorphism $\alpha$ of $M$ fixing each $\lambda(k)$, $k\in\kappa$, and a word $w'\in\mathbb F_n$ with
--
--   $$\|\alpha(\lambda(i))-\lambda(i)\|<\varepsilon\quad(i\in\mathrm{Fin}\,n),\qquad\|\alpha(\lambda(w'))-c\|_2<\varepsilon.$$
--
--   This is the form of Proposition 5.1 of the paper used for the infinite-rank factor.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FiniteActive.one_step_from_laurent`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/FiniteActive.lean#L316

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

end

open UnitaryEvaluation

theorem one_step_from_laurent {κ : Type uκ} [DecidableEq κ]
    (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n ⊕ κ))) l) -
        (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : Ambient (Fin n) κ ≃⋆ₐ[ℂ] Ambient (Fin n) κ,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : κ, α (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      ∃ w : FreeGroup (Fin n),
        (∀ i : Fin n, ‖α (groupUnitary (FreeGroup.of (some (Sum.inl i)))) -
          groupUnitary (FreeGroup.of (some (Sum.inl i)))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
          groupUnitary (FreeGroup.of none)) < ε := by
  sorry

end FreeGroupFactorMain.FiniteActive
end
end OAI
