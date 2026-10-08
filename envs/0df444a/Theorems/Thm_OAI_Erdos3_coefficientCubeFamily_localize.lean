-- Prove2me | Theorems.Thm_OAI_Erdos3_coefficientCubeFamily_localize
-- name    : OAI.Erdos3.coefficientCubeFamily_localize
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:06:00.961978+00:00
-- url     : https://prove2.me/theorems/2a30fac1-71bc-49a1-aeb0-ed23cf7ce7b0
-- title:
--   A biased test on a family of localization data localizes to residue cells
-- statement:
--   Let $n$ be a natural number and $I$ a finite type with decidable equality. Let $c$ be a `ScalarCubeLocalizationData Empty` and $d_0,\dots,d_{n-1}$ be `ScalarCubeLocalizationData I` (a `ScalarCubeLocalizationData I` is a structure bundling a length, residue moduli and residues indexed by $\mathrm{Option}\ I$, a bounded Lipschitz weight and a mesh, with derived objects: the probability weights `source` on `IntegerScalarCubeBox I length`, the rescaling map `point` $z\mapsto z/\mathrm{length}$ into $\mathbb{R}^{\mathrm{Option}\ I}$, natural numbers `cellCount` and `cellLength`, cell positions `cell k t` $\in\mathbb{R}^{\mathrm{Option}\ I}$ for $k : \mathrm{Option}\ I\to\{0,\dots,\mathrm{cellCount}-1\}$ and $t : \mathrm{Option}\ I\to\{0,\dots,\mathrm{cellLength}-1\}$, and a real-valued function `error`). Let $\tau_0,\dots,\tau_{n+1}$ be real numbers with $\tau_1,\dots,\tau_{n+1}>0$, $c.\mathrm{error}(\tau_1)\le\tau_0$, and $d_j.\mathrm{error}(\tau_{j+2})\le\tau_{j+1}$ for every $j<n$. Let $F : \mathbb{R}^{\mathrm{Option}\ \mathrm{Empty}}\times(\{0,\dots,n-1\}\to\mathbb{R}^{\mathrm{Option}\ I})\to\mathbb{C}$ with $|F|\le 1$ everywhere, and assume the bias
--   $$\tau_0\le\Big|\,\mathbb{E}_{z\sim c.\mathrm{source}}\ \mathbb{E}_{x\sim\prod_j d_j.\mathrm{source}}\ F\big(c.\mathrm{point}(z),\,(d_j.\mathrm{point}(x_j))_{j}\big)\Big|,$$
--   where the expectations are the `complexMean`s of `c.source` and of the product weights `FiniteProbabilityWeights.pi` of the $d_j.\mathrm{source}$. Then there exist $a : \mathrm{Option}\ \mathrm{Empty}\to\{0,\dots,c.\mathrm{cellCount}-1\}$ and, for each $j$, $k_j : \mathrm{Option}\ I\to\{0,\dots,d_j.\mathrm{cellCount}-1\}$ such that: every $c.\mathrm{cell}(a,t)$ lies in `scalarCubeDomain Empty`; every $d_j.\mathrm{cell}(k_j,t)$ lies in `scalarCubeDomain I` (`scalarCubeDomain α` is the set of $y\in\mathbb{R}^{\mathrm{Option}\ \alpha}$ with $y_{\mathrm{none}}+\sum_{i\in t}y_{\mathrm{some}\ i}\in(0,1)$ for every $t\subseteq\alpha$); and
--   $$\tau_{n+1}\le\Big|\,\mathbb{E}_{t}\ \mathbb{E}_{u}\ F\big(c.\mathrm{cell}(a,t),\,(d_j.\mathrm{cell}(k_j,u_j))_j\big)\Big|,$$
--   with $t$ uniform over $\mathrm{Option}\ \mathrm{Empty}\to\{0,\dots,c.\mathrm{cellLength}-1\}$ and $u$ uniform over the families $(u_j)_j$ with $u_j : \mathrm{Option}\ I\to\{0,\dots,d_j.\mathrm{cellLength}-1\}$.
--
--   Lean: `OAI.Erdos3.coefficientCubeFamily_localize` in `lean/OAI/Combinatorics/Progressions/Estimates/CoefficientFamilyLocalization.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CoefficientFamilyLocalization.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficientCubeFamily_localize {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (F : (Option Empty → ℝ) → (Fin n → Option I → ℝ) → ℂ)
    (hF : ∀ x y, ‖F x y‖ ≤ 1)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => F (c.point z) (fun j => (d j).point (x j))))‖) :
    ∃ a : Option Empty → Fin c.cellCount, ∃ k : ∀ j, Option I → Fin (d j).cellCount,
      (∀ t : Option Empty → Fin c.cellLength, c.cell a t ∈ scalarCubeDomain Empty) ∧
      (∀ j (t : Option I → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain I) ∧
      τ (Fin.last (n + 1)) ≤
        ‖𝔼 t : Option Empty → Fin c.cellLength, 𝔼 u : ∀ j, Option I → Fin (d j).cellLength,
          F (c.cell a t) (fun j => (d j).cell (k j) (u j))‖ := by
  sorry

end Erdos3
end
end OAI
