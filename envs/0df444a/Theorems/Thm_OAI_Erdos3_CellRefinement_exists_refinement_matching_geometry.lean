-- Prove2me | Theorems.Thm_OAI_Erdos3_CellRefinement_exists_refinement_matching_geometry
-- name    : OAI.Erdos3.CellRefinement.exists_refinement_matching_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T18:20:50.709976+00:00
-- url     : https://prove2.me/theorems/635e3c76-21ce-484e-a952-3fbd31f729d9
-- title:
--   A rank-regular Bohr set refines to a local/inner pair matching the bilinear integral
-- statement:
--   Let $N$ be a positive natural number (`[NeZero N]`). A `CyclicBohr.Set N` is OpenAI's structure bundling a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\rho \ge 0$; its `carrier` is the finite set of $x \in \mathbb{Z}/N$ with $\|1 - \chi_r(x)\| \le \rho$ for every frequency $r$ (where $\chi_r$ is the additive character `CyclicBohr.character r`), its `rank` is the number of frequencies, `B.ndilate t` (for $t \in \mathbb{R}_{\ge 0}$) is the Bohr set with the same frequencies and radius $t \cdot \rho$, and `IsRankRegular` is OpenAI's regularity predicate (for every $\kappa \le 1/(100 d)$, $d = 2\max(\mathrm{rank},1)$, the carriers of the dilates by $1-\kappa$ and $1+\kappa$ have sizes within a factor $1 \mp 100 d \kappa$ of the carrier). Let $B$ be such a Bohr set with $0 < \rho_B$, `B.IsRankRegular`, $\rho_B \le 2$ and $1 \le \operatorname{rank} B$. Let $W, Q, E, M, p, H, J, T, R, \delta$ be reals and $\mathrm{scale} \in \mathbb{R}_{\ge 0}$, with $0 \le W \le e^{Q}$, $0 \le Q$, $0 \le E$, $0 \le M \le e^{p}$, $1 \le p$, $0 \le H$, $0 \le J$, $0 \le T$, $0 \le R$, $0 < \delta$, $e^{-R} \le \rho_B$ and $e^{-T} \le \mathrm{scale}$. Put $c = $ `localMomentGain δ`, $\kappa = $ `outerMatchingScale (rank B) W (exp (-E)) scale`, $\tau = $ `coordinatedMatchingScale (rank B) M δ c κ` (both in $\mathbb{R}_{\ge 0}$), $D = $ `matchingWidthLoss (rank B) p (outerMatchingScaleLoss (rank B) Q E T) δ c` and $w = \rho_B \cdot \exp(-$`refinementMatchingWidthLoss (rank B) p H Q E J T δ`$)$; these are OpenAI's explicit real-valued (or $\mathbb{R}_{\ge 0}$-valued) scale and loss functions. Then $0 \le R + D$, and there exist Bohr sets $L, S$ such that: $L$ has the frequencies of $B$ and $S$ those of $L$; $L$ and $S$ are rank-regular; $0 < \rho_L$, $0 < \rho_S$, $\rho_S \le \rho_L$, $\rho_S \le 1$ and $1 \le \operatorname{rank} S$; `Peeling.admissibleBohrShape B scale (unbalancedRankExtra c p H) w L` holds (the predicate: $L$ is rank-regular, its carrier lies in that of `B.ndilate scale`, $\operatorname{rank} L \le \operatorname{rank} B + $ `unbalancedRankExtra c p H` (a natural number), and $w \le \rho_L$); the carrier of $S$ lies in the carrier of `B.ndilate scale`; $\operatorname{rank} S + e \le \operatorname{rank} B + e$ with $e = $ `unbalancedRankExtra c p H`; $w \le \rho_S \cdot \exp(-$`unbalancedReturnWidthLoss (rank S) c p H Q J`$)$; $e^{-(R+D)} \le \rho_S$; the carrier of $S$ lies in the carriers of `L.ndilate τ` and of `L.ndilate (controlledLocalMomentScale (rank L) M δ)`; $\tau + \tau \le 1/(100 \cdot 2\max(\operatorname{rank} L, 1))$ in $\mathbb{R}_{\ge 0}$; $M^2 \cdot (400 \max(\operatorname{rank} L, 1) \cdot (\tau + \tau)) \le c/32$; and for all functions $a, f, g : \mathbb{Z}/N \to \mathbb{R}$ with $|a(x)| \le W$, $0 \le f(x) \le 1$ and $0 \le g(x) \le 1$ for all $x$,
--   $$\bigl|\,\texttt{bilinearIntegral}(B, B, a, f, g) - \texttt{parentTruncatedIntegral}(B, B, L, S, a, f, g)\,\bigr| \le e^{-E},$$
--   where the sets are the carriers, `CellRefinement.bilinearIntegral A B a f g` is the average over $x \in A$, $y \in B$ of $f(x)\,g(y)\,a(x+y)$, and `CellRefinement.parentTruncatedIntegral A B L S a f g` is the average over $x \in A$, $y \in B$ of `matchedIntegral L S` applied to $z \mapsto a(x+y+z)$ and to the restrictions to $L$ of $r \mapsto f(x+r)$ and $r \mapsto g(y+r)$ (`matchedIntegral L S a f g` being the average over $r \in L$, $s, t \in S$ of $f(r)\,g(-r+s+t)\,a(s+t)$).
--
--   Lean: `OAI.Erdos3.CellRefinement.exists_refinement_matching_geometry` in `lean/OAI/Combinatorics/Progressions/Estimates/RefinementMatchingGeometry.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RefinementMatchingGeometry.lean#L616

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_refinement_matching_geometry
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (hBwidth : B.radius ≤ 2) (hBrank : 1 ≤ B.rank)
    {W Q E M p H J T R delta : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp p) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hJ : 0 ≤ J) (hT : 0 ≤ T) (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hBwide : Real.exp (-R) ≤ B.radius) (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    let c := localMomentGain delta
    let kappa := outerMatchingScale B.rank W (Real.exp (-E)) scale
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    let D := matchingWidthLoss B.rank p (outerMatchingScaleLoss B.rank Q E T) delta c
    let w := B.radius * Real.exp (-refinementMatchingWidthLoss B.rank p H Q E J T delta)
    0 ≤ R + D ∧ ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      S.radius ≤ L.radius ∧ S.radius ≤ 1 ∧ 1 ≤ S.rank ∧
      Peeling.admissibleBohrShape B scale (unbalancedRankExtra c p H) w L ∧
      S.carrier ⊆ (B.ndilate scale).carrier ∧
      S.rank + unbalancedRankExtra c p H ≤ B.rank + unbalancedRankExtra c p H ∧
      w ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q J) ∧
      Real.exp (-(R + D)) ≤ S.radius ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  sorry

end Erdos3.CellRefinement
end
end OAI
