-- Prove2me | Theorems.Thm_OAI_Erdos3_integerBox_joint_error_of_window_tests
-- name    : OAI.Erdos3.integerBox_joint_error_of_window_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:41:17.974859+00:00
-- url     : https://prove2.me/theorems/45870b80-3c83-405a-88f9-0e8c71a95c35
-- title:
--   Joint box averages inherit a bound from all [0,1]-weighted window tests
-- statement:
--   Let $I,J$ be finite types with decidable equality, $\mathrm{lo},\mathrm{hi}\colon I\to\mathbb Z$ with $\mathrm{lo}_i<\mathrm{hi}_i$, and $\mathrm{parLo},\mathrm{parHi}\colon J\to\mathbb Z$ with $\mathrm{parLo}_j<\mathrm{parHi}_j$. Write $Z=\prod_i\{\mathrm{lo}_i,\dots,\mathrm{hi}_i-1\}$ and $\mathcal T=\prod_j\{\mathrm{parLo}_j,\dots,\mathrm{parHi}_j-1\}$. Let $f\colon\mathbb Z^I\times\mathcal T\to\mathbb R$ and $\mathrm{accuracy}\in\mathbb R$, and assume (`htest`) that for every $v\colon\mathbb Z^I\to[0,1]$,
--   $$\Big|\mathbb E_{z\in Z}\,v(z)\,\mathbb E_{t\in\mathcal T}f(z,t)\Big|\le\mathrm{accuracy},$$
--   the averages being uniform. Let $w\colon\mathbb Z^I\to\mathbb R$ with $0\le w(z)\le1$ for all $z\in Z$. Then, for $t$ and $x$ drawn independently and uniformly from $\mathcal T$ and $Z$ (the product `prod` of `integerBoxUniformWeights parLo parHi hparam` and `integerBoxUniformWeights lo hi hsource`), $\big|\mathbb E\,[\,w(x)\,f(x,t)\,]\big|\le\mathrm{accuracy}$.
--
--   Lean: `OAI.Erdos3.integerBox_joint_error_of_window_tests` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshRetention.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B016` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineMeshRetention.lean#L468

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBox_joint_error_of_window_tests
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) (accuracy : ℝ)
    (htest : ∀ v : (I → ℤ) → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) →
      |𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), v z * (𝔼 t, f z t)| ≤ accuracy)
    (w : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (lo i) (hi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) :
    |((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1)| ≤ accuracy := by
  sorry

end Erdos3
end
end OAI
