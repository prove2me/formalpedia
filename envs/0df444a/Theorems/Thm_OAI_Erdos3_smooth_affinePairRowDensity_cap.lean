-- Prove2me | Theorems.Thm_OAI_Erdos3_smooth_affinePairRowDensity_cap
-- name    : OAI.Erdos3.smooth_affinePairRowDensity_cap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:29:21.179222+00:00
-- url     : https://prove2.me/theorems/a37625d0-6092-456d-acc0-ee3aad294ef2
-- title:
--   Uniform bound on the smooth affine pair row density
-- statement:
--   Let $J$ be a finite type with decidable equality, $t,u\colon J\to\mathbb Z$ and $k\in J$ with $u_k-t_k\ne0$ (`hne`), and let $H,L,C,\kappa$ be reals with $0<H$, $0<L$, $1\le C$, $0<\kappa$, $|t_k/L|\le C$, $|u_k/L|\le C$ and $\kappa\le|(u_k-t_k)/L|$. Then for every $y\in\mathbb R^2$ (as `Fin 2 → ℝ`),
--   $$\big|\texttt{affinePairRowDensity}\ t\ u\ k\ \mathit{hne}\ H\ L\ \mathit{hH}\ \mathit{hL}\ (\texttt{splitSmoothProductProfile}\ \{j\,//\,j\ne k\}\ (\texttt{Fin}\ 2))\ y\big|\le 2\,(4C/\kappa)^2\,2^{|\{j\in J:j\ne k\}|}.$$
--   Here `affinePairRowDensity t u k hne H L hH hL f` is the real function on $\mathbb R^2$ given by `normalizedFiberDensity` for the pivot matrix $\begin{pmatrix}1&t_k\\1&u_k\end{pmatrix}$, the free integer columns $(t_j,u_j)_{j\ne k}$ and the scale parameters $S=(H,H/L)$, $P\equiv H$ (indexed by $\mathrm{Fin}\,2$) and $T\equiv H/L$ (indexed by $\{j:j\ne k\}$), applied to the profile $f$; and `splitSmoothProductProfile {j // j ≠ k} (Fin 2)` is the function $(a,b)\mapsto \prod_{j\ne k}\phi(a_j)\cdot\prod_{i<2}\phi(b_i)$ for OpenAI's one-variable profile $\phi=$ `smoothProbabilityProfile`.
--
--   Lean: `OAI.Erdos3.smooth_affinePairRowDensity_cap` in `lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSmoothPairLaw.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AnisotropicSmoothPairLaw.lean#L145

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smooth_affinePairRowDensity_cap {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ : ℝ} (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (y : Fin 2 → ℝ) :
    |affinePairRowDensity t u k hne H L hH hL
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) y| ≤
      2 * (4 * C / κ) ^ 2 * (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} := by
  sorry

end Erdos3
end
end OAI
