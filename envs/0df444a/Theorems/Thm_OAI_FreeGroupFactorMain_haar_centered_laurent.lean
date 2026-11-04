-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_haar_centered_laurent
-- name    : OAI.FreeGroupFactorMain.haar_centered_laurent
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:54:26.465428+00:00
-- url     : https://prove2.me/theorems/7898dd22-daea-4d27-a742-cc4955070650
-- title:
--   Centered Laurent approximation of the logarithm of a Haar unitary
-- statement:
--   Throughout, $L(G)$ is the group von Neumann algebra of a discrete group $G$ acting on $\ell^2(G)$, with canonical trace $\tau(x)=\langle x\delta_e,\delta_e\rangle$, left-regular unitaries $\lambda(g)$, and $\|x\|_2=\|x\delta_e\|_{\ell^2}$. Let $G$ be a group and $C\in L(G)$ a unitary with $\tau(C^m)=0$ for every integer $m\ne0$. For every $\varepsilon>0$ there are a finitely supported $k:\mathbb Z\to\mathbb C$ with $k(0)=0$, and a scalar $z$ of modulus one, such that $V=\sum_m k(m)C^m$ is self-adjoint, $\|V\|\le 2(\pi+1)$, and
--
--   $$\|e^{iV}-zC\|_2<\varepsilon.$$
--
--   This replaces the bounded Borel logarithm of the paper's $S=\arg C$ by a Laurent polynomial with uniformly bounded norm.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.haar_centered_laurent`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FreeGroupFactor/LaurentApproximation.lean#L385

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe uA uG

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.MobiusLog
variable {A : Type uA} [CommCStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.MobiusLog
namespace FreeGroupFactorMain.ElementalMobius
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.ElementalMobius
namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

end FreeGroupFactorMain

open scoped BigOperators
namespace FreeGroupFactorMain.LaurentApprox

section
variable {A : Type uA} [CStarAlgebra A]

end

variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.LaurentApprox

namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

theorem haar_centered_laurent (C : unitary (groupVonNeumann G))
    (hτ : ∀ m : ℤ, canonicalTrace ((C^m : unitary (groupVonNeumann G)) : groupVonNeumann G) =
      if m = 0 then 1 else 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℤ →₀ ℂ, k 0 = 0 ∧ IsSelfAdjoint (LaurentApprox.value C k) ∧
      ‖LaurentApprox.value C k‖ ≤ 2*(Real.pi+1) ∧ ∃ z : unitary ℂ,
      twoNorm (NormedSpace.exp (Complex.I • LaurentApprox.value C k) - (z : ℂ) • (C : groupVonNeumann G)) < ε := by
  sorry

end FreeGroupFactorMain
end
end OAI
