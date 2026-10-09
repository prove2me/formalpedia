-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalBox_pair_kernel_grid_error
-- name    : OAI.Erdos3.physicalBox_pair_kernel_grid_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:26:57.727509+00:00
-- url     : https://prove2.me/theorems/2390dacd-8004-4630-95c3-bbbf3a594a85
-- title:
--   Moving pair locations to their cell corners changes the kernel by at most Lip times ρ
-- statement:
--   Let $J$ and $I$ be finite types with decidable equality. Let $t,u\colon J\to\mathbb Z$ and $k\in J$ with $u_k-t_k\ne 0$ (`hne`); let $H\colon I\to\mathbb R$ with $H_i>0$ for all $i$ and $L>0$; and let $C,\kappa,\rho$ be reals with $1\le C$, $0<\kappa$, $0\le\rho$, $|t_k/L|\le C$, $|u_k/L|\le C$ and $\kappa\le|(u_k-t_k)/L|$. Let $b\colon\mathrm{Option}\,J\times I\to\mathbb Z$, $\mathrm{lo}\colon I\to\mathbb Z$, $N\colon I\to\mathbb N$, and for each $i$ let $P_i$ be a `FiniteProgressionPartition (N i)` (a partition of $\{0,\dots,N_i-1\}$ into labelled progressions, each with a start, step and length) all of whose blocks have step $1$ and length at most $\rho H_i$. Then for all $x,y$ in `translatedIntegerBox lo N` (the integer points $z$ with $\mathrm{lo}_i\le z_i<\mathrm{lo}_i+N_i$ for all $i$),
--   $$\big|K_b(x,y)-K_b(\bar x,\bar y)\big|\le \texttt{smoothPairKernelLip}\ |I|\ k\ C\ \kappa\cdot\rho,$$
--   where $K_b(x,y)$ is `shiftedPairLocationKernel t u k hne H L hH hL b x y`, and $\bar x_i=$ `intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i)` $=\mathrm{lo}_i+\mathrm{start}$ of the block of $P_i$ that `physicalBoxCell` assigns to $x$ in coordinate $i$ (similarly $\bar y$). `shiftedPairLocationKernel` is the product over $i$ of `affinePairRowDensity` (a real function on $\mathbb R^2$ built from $t,u,k,H_i,L$ and `splitSmoothProductProfile`) evaluated at $((x_i,y_i)-(s_t(i),s_u(i)))/H_i$, with $s_t(i)=b(\mathrm{none},i)+\sum_j t_j\,b(\mathrm{some}\ j,i)$ and likewise $s_u$. The constant `smoothPairKernelLip n k C κ` is the nonnegative real $n\cdot$ `smoothPairKernelBaseLip k C κ` $\cdot$ `smoothPairKernelCap n k C κ`, where the base Lipschitz constant is $\max(0,\,2(4C/\kappa)^3\,\ell_k\,2^{|\{j:j\ne k\}|})$ with $\ell_k=$ `smoothPairRowLipschitz k` $=(|\{j:j\ne k\}|+2)\cdot$ `probabilityProfileLipschitz`, and the cap is $\big(\max(0,1+2(4C/\kappa)^2\,2^{|\{j:j\ne k\}|})\big)^n$.
--
--   Lean: `OAI.Erdos3.physicalBox_pair_kernel_grid_error` in `lean/OAI/Combinatorics/Progressions/Linear/PhysicalBoxKernel.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/PhysicalBoxKernel.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem physicalBox_pair_kernel_grid_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ ρ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (b : Option J × I → ℤ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1)
    (hlength : ∀ i c, ((P i).length c : ℝ) ≤ ρ * H i)
    (x y : translatedIntegerBox lo N) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x.val y.val -
      shiftedPairLocationKernel t u k hne H L hH hL b
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i))
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P y i))| ≤
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ := by
  sorry

end Erdos3
end
end OAI
