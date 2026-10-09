-- Prove2me | Theorems.Thm_OAI_Erdos3_affineSampleKernel_centered_sq_of_inverse_le
-- name    : OAI.Erdos3.affineSampleKernel_centered_sq_of_inverse_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:16.563874+00:00
-- url     : https://prove2.me/theorems/d0470b07-cf61-4c74-9a29-fe5fdcfad07d
-- title:
--   Random affine sample kernels contract centered functions in mean square
-- statement:
--   Let $J$ and $I$ be finite types and let $q, p, a$ be natural numbers with $q \neq 0$ (`[NeZero q]`), $p$ prime and $q = p^a$; suppose $J$ has at least $2$ elements. Let $\kappa$ be a real number with $0 \le \kappa$ and $p^{-1} \le \kappa$. Let $f : (I \to \mathbb{Z}/q) \to \mathbb{R}$ have mean $0$ under the uniform distribution on $I \to \mathbb{Z}/q$. A `FiniteProbabilityWeights Ω` is OpenAI's structure bundling a probability weight function on a finite type $\Omega$, with `mean` the weighted sum $\sum_x w(x) f(x)$ and `uniform Ω` the uniform weights. For $z : \mathrm{Option}\,J \times I \to \mathbb{Z}/q$, `affineSampleKernel z` is the probability weights on $I \to \mathbb{Z}/q$ given by the law of $z_0 + \sum_{j \in J} t_j\, z_j$, where $t$ is uniform on $J \to \mathbb{Z}/q$, $z_0 = (i \mapsto z(\mathrm{none}, i))$ and $z_j = (i \mapsto z(\mathrm{some}\ j, i))$. Then
--   $$\mathbb{E}_{z}\Bigl[\bigl(\mathbb{E}_{\texttt{affineSampleKernel}\ z} f\bigr)^2\Bigr] \le \kappa^2\, \mathbb{E}_{y}\bigl[f(y)^2\bigr],$$
--   with $z$ uniform on $\mathrm{Option}\,J \times I \to \mathbb{Z}/q$ and $y$ uniform on $I \to \mathbb{Z}/q$.
--
--   Lean: `OAI.Erdos3.affineSampleKernel_centered_sq_of_inverse_le` in `lean/OAI/Combinatorics/Progressions/Lattices/RetainedPhysicalCRT.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/RetainedPhysicalCRT.lean#L143

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem affineSampleKernel_centered_sq_of_inverse_le {J I : Type*} [Fintype J] [Fintype I]
    {q p a : ℕ} [NeZero q] {κ : ℝ} (hp : p.Prime) (hq : q = p ^ a)
    (hJ : 2 ≤ Fintype.card J) (hκ : 0 ≤ κ) (hlarge : (p : ℝ)⁻¹ ≤ κ)
    (f : (I → ZMod q) → ℝ) (hf : (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f = 0) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f ^ 2) ≤
      κ ^ 2 * (FiniteProbabilityWeights.uniform (I → ZMod q)).mean (fun y => f y ^ 2) := by
  sorry

end Erdos3
end
end OAI
