-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarCubeFamily_localize
-- name    : OAI.Erdos3.scalarCubeFamily_localize
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:29:41.199206+00:00
-- url     : https://prove2.me/theorems/24d77406-90a6-4e33-a69a-ad7f13ba0144
-- title:
--   A biased test on a product of localization data localizes to residue cells
-- statement:
--   Let $n$ be a natural number and $I_0,\dots,I_{n-1}$ finite types with decidable equality. For each $j<n$ let $d_j$ be a `ScalarCubeLocalizationData (I j)` (a structure bundling a length, residue moduli and residues indexed by $\mathrm{Option}\ I_j$, a bounded Lipschitz weight and a mesh, with derived objects: the probability weights `source` on `IntegerScalarCubeBox (I j) length`, the rescaling map `point` $z\mapsto z/\mathrm{length}$ into $\mathbb{R}^{\mathrm{Option}\ I_j}$, natural numbers `cellCount` and `cellLength`, cell positions `cell k t` $\in\mathbb{R}^{\mathrm{Option}\ I_j}$ for $k : \mathrm{Option}\ I_j\to\{0,\dots,\mathrm{cellCount}-1\}$ and $t : \mathrm{Option}\ I_j\to\{0,\dots,\mathrm{cellLength}-1\}$, and a real-valued function `error`). Let $\tau_0,\dots,\tau_n$ be real numbers with $\tau_{j+1}>0$ and $d_j.\mathrm{error}(\tau_{j+1})\le\tau_j$ for every $j<n$. Let $F$ be a function from families $(y_j)_{j<n}$ with $y_j\in\mathbb{R}^{\mathrm{Option}\ I_j}$ to $\mathbb{C}$, with $|F|\le 1$ everywhere, and assume
--   $$\tau_0\le\Big|\,\mathbb{E}_{z\sim\prod_j d_j.\mathrm{source}}\ F\big((d_j.\mathrm{point}(z_j))_j\big)\Big|,$$
--   the expectation being the `complexMean` of the product weights `FiniteProbabilityWeights.pi` of the $d_j.\mathrm{source}$. Then there exist $k_j : \mathrm{Option}\ I_j\to\{0,\dots,d_j.\mathrm{cellCount}-1\}$ for each $j$ such that every $d_j.\mathrm{cell}(k_j,t)$ lies in `scalarCubeDomain (I j)` (the set of $y\in\mathbb{R}^{\mathrm{Option}\ I_j}$ with $y_{\mathrm{none}}+\sum_{i\in t}y_{\mathrm{some}\ i}\in(0,1)$ for every $t\subseteq I_j$), and
--   $$\tau_n\le\Big|\,\mathbb{E}_{t}\ F\big((d_j.\mathrm{cell}(k_j,t_j))_j\big)\Big|,$$
--   with $t$ uniform over the families $(t_j)_j$, $t_j : \mathrm{Option}\ I_j\to\{0,\dots,d_j.\mathrm{cellLength}-1\}$.
--
--   Lean: `OAI.Erdos3.scalarCubeFamily_localize` in `lean/OAI/Combinatorics/Progressions/Estimates/CoefficientSliceEmbedding.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CoefficientSliceEmbedding.lean#L322

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeFamily_localize {n : ℕ} (I : Fin n → Type*)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (d : ∀ j, ScalarCubeLocalizationData (I j)) (τ : Fin (n + 1) → ℝ)
    (hτ : ∀ j : Fin n, 0 < τ j.succ) (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (F : (∀ j, Option (I j) → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖) :
    ∃ k : ∀ j, Option (I j) → Fin (d j).cellCount,
      (∀ j (t : Option (I j) → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain (I j)) ∧
      τ (Fin.last n) ≤ ‖𝔼 t : ∀ j, Option (I j) → Fin (d j).cellLength,
        F (fun j => (d j).cell (k j) (t j))‖ := by
  sorry

end Erdos3
end
end OAI
