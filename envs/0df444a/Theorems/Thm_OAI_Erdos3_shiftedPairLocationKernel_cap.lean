-- Prove2me | Theorems.Thm_OAI_Erdos3_shiftedPairLocationKernel_cap
-- name    : OAI.Erdos3.shiftedPairLocationKernel_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:26:47.571443+00:00
-- url     : https://prove2.me/theorems/d87156a6-e6b3-4bc8-83f7-fd02af08c9cc
-- title:
--   The shifted pair location kernel is bounded by the smooth pair kernel cap
-- statement:
--   Let $J$ be a finite type with decidable equality and $I$ a finite type. Let $t,u\colon J\to\mathbb Z$ and $k\in J$ with $u_k-t_k\ne 0$ (`hne`); let $H\colon I\to\mathbb R$ with $H_i>0$ for all $i$ and $L>0$; and let $C,\kappa$ be reals with $1\le C$, $0<\kappa$, $|t_k/L|\le C$, $|u_k/L|\le C$ and $\kappa\le|(u_k-t_k)/L|$. Then for every $b\colon \mathrm{Option}\,J\times I\to\mathbb Z$ and all $x,y\colon I\to\mathbb Z$,
--   $$|\texttt{shiftedPairLocationKernel}\ t\ u\ k\ \mathit{hne}\ H\ L\ \mathit{hH}\ \mathit{hL}\ b\ x\ y|\le \texttt{smoothPairKernelCap}\ |I|\ k\ C\ \kappa .$$
--   Here `shiftedPairLocationKernel … b x y` is the product over $i\in I$ of `affinePairRowDensity t u k hne (H i) L … (splitSmoothProductProfile {j // j ≠ k} (Fin 2))` evaluated at the point $\big((x_i,y_i)-(s_t(i),s_u(i))\big)/H_i\in\mathbb R^2$, where $s_t(i)=b(\mathrm{none},i)+\sum_{j\in J}t_j\,b(\mathrm{some}\ j,i)$ and likewise $s_u$ (`smoothAffinePairRows t u b`); `affinePairRowDensity` is a real function on $\mathbb R^2$ (a `normalizedFiberDensity` built from the pivot matrix $\begin{pmatrix}1&t_k\\1&u_k\end{pmatrix}$, the free columns $(t_j,u_j)_{j\ne k}$ and the scales $H$, $H/L$), and `splitSmoothProductProfile` is a product of smooth one-variable profiles. The cap `smoothPairKernelCap n k C κ` is the nonnegative real $\big(\max(0,\,1+2(4C/\kappa)^2\,2^{|\{j\in J:j\ne k\}|})\big)^n$.
--
--   Lean: `OAI.Erdos3.shiftedPairLocationKernel_cap` in `lean/OAI/Combinatorics/Progressions/Sampling/SmoothPairPhysicalGrid.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/SmoothPairPhysicalGrid.lean#L45

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem shiftedPairLocationKernel_cap {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (b : Option J × I → ℤ) (x y : I → ℤ) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x y| ≤
      smoothPairKernelCap (Fintype.card I) k C κ := by
  sorry

end Erdos3
end
end OAI
