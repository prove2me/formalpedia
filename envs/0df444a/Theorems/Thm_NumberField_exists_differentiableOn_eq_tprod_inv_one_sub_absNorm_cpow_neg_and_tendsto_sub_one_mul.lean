-- Prove2me | Theorems.Thm_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
-- name    : NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/2cbb8201-7b85-5846-a5b0-087eb9bf6290
-- title:
--   Partial Dedekind zeta function: continuation and simple pole at s=1
-- statement:
--   Let $K$ be a number field and let $T$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$. The assertion is the existence of a function $L\colon\mathbb{C}\to\mathbb{C}$ with three properties. First, $L$ is complex-differentiable on the set $\{s\in\mathbb{C} : \tfrac12<\operatorname{Re} s\}\setminus\{1\}$ (differentiability in the `DifferentiableOn` sense, i.e. within that set). Second, for every $s$ with $\operatorname{Re} s>1$, the value $L(s)$ equals the unconditional complex infinite product $\prod'_{v\notin T}\bigl(1-(\mathrm{N}v)^{-s}\bigr)^{-1}$, indexed by the subtype of primes $v$ of $\mathcal{O}_K$ not lying in $T$, where $\mathrm{N}v$ denotes the absolute norm $\mathrm{Ideal.absNorm}$ of the ideal underlying $v$, viewed as a natural number and then as a complex number, and $(\cdot)^{-s}$ is the complex power; in particular the product is asserted to be multipliable there with this value. Third, there is a complex number $\kappa\neq 0$ such that $(s-1)L(s)$ tends to $\kappa$ as $s\to 1$ along the punctured neighbourhood filter $\mathcal{N}[\neq]1$. No claim is made about $L$ outside the half-plane $\operatorname{Re} s>\tfrac12$, nor is $L$ pinned down uniquely.
--
--   This is the analytic continuation of the Dedekind zeta function of $K$ with the Euler factors at the primes of $T$ removed, together with the statement that it has a simple pole at $s=1$ with non-zero residue; only continuation to $\operatorname{Re} s>\tfrac12$ is recorded, which is all that later arguments need. It is deduced from the package of properties of the completed zeta function $\Lambda_K$ provided by [`NumberField.exists_completedDedekindZeta_package`](thm.html#NumberField.exists_completedDedekindZeta_package), and is used in the global Tate-theoretic input (non-vanishing statements for partial Euler products attached to unitary characters) and in the analytic continuation of Weyl intertwining integrals for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
      (∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 κ) := by sorry
