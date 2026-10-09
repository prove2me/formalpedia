-- Prove2me | Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_unbalanced_bohr_second_moment_at_scale
-- name    : OAI.Erdos3.LocalConvolution.exists_unbalanced_bohr_second_moment_at_scale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:03:31.749999+00:00
-- url     : https://prove2.me/theorems/f50a7f18-4b7f-4ad8-bc7d-e82c1d2b5cf8
-- title:
--   A large difference moment yields a Bohr cell with large second moment at a given scale
-- statement:
--   Let $N$ be a positive natural number (`[NeZero N]`). A `CyclicBohr.Set N` is OpenAI's structure bundling a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\rho \ge 0$; its `carrier` is the finite set of $x$ with $\|1 - \chi_r(x)\| \le \rho$ for every frequency $r$ ($\chi_r$ the additive character `CyclicBohr.character r`), its `rank` is the number of frequencies, `ndilate t` scales the radius by $t \in \mathbb{R}_{\ge 0}$, and `IsRankRegular` is OpenAI's regularity predicate on carrier sizes of the dilates by $1 \pm \kappa$; below a Bohr set stands for its carrier where a set is meant.
--
--   Let $L, S$ be Bohr sets with $L$ rank-regular, $0 < \rho_S \le 1$, $S$ rank-regular and $1 \le \operatorname{rank} S$. Let $\kappa_0 \in \mathbb{R}_{\ge 0}$ with $S \subseteq$ `L.ndilate κ₀` and $\kappa_0 \le 1/(100 \cdot 2\max(\operatorname{rank} L, 1))$. Let $f : \mathbb{Z}/N \to \mathbb{R}$ vanish off $L$, and let $M, c, p, H$ be reals with $0 < M$, $0 < c \le 1$, $1 \le p$, $0 \le H$, $M \le e^{p}$, $0 \le f(x) \le M$ for all $x$, and $200 \max(\operatorname{rank} L, 1)\, \kappa_0 M^2 \le c/64$. Let $q$ be a positive even natural number with $q \le H p$ such that $1 + c \le$ `differenceLp S (correlation L f f) q` (the average $(\mathbb{E}_{(s,t) \in S \times S} |\phi(s - t)|^q)^{1/q}$ of $\phi = $ `correlation L f f`, $\phi(t) = \sum_x f(x+t) f(x) / |L|$) and $(1 + c/4)^q \le \tfrac{c/64}{2} (1 + c/2)^q$. Let $\kappa \in \mathbb{R}_{\ge 0}$ with $0 < \kappa \le$ `localizedAverageScale (rank S) (M^(2q)) ((1+c)^q - (1+c/2)^q)`, where `localizedAverageScale r R ε` is the $\mathbb{R}_{\ge 0}$-valued scale $\max\bigl(0, \min\bigl(\tfrac{1}{200\max(r,1)}, \tfrac{\varepsilon}{400\max(r,1)(R+1)}\bigr)\bigr)$. Put $D = (3H + 1) p^2$ and $c' = $ `almostPeriodicityWidthConstant (c / 64)` (an explicit real constant). Then there is a Bohr set $C$ that is rank-regular with $0 < \rho_C \le 1$, $C \subseteq S$, $C \subseteq$ `S.ndilate κ`, $\operatorname{rank} C \le \operatorname{rank} S + c' (1 + D)^4$,
--   $$\Bigl(\kappa \cdot \texttt{localizedAverageScale}(\operatorname{rank} C, M^2, c/64) \cdot \rho_S / 8\Bigr) \exp\bigl(-c' (1 + D + \log(2 + \operatorname{rank} S))\bigr) \le \rho_C,$$
--   and
--   $$1 + c/16 \le \mathbb{E}_{x \in L}\, \bigl(\texttt{cellAverage}\ C\ f\ x\bigr)^2, \qquad \texttt{cellAverage}\ C\ f\ x = \mathbb{E}_{t \in C} f(x + t).$$
--
--   Lean: `OAI.Erdos3.LocalConvolution.exists_unbalanced_bohr_second_moment_at_scale` in `lean/OAI/Combinatorics/Progressions/Fourier/UnbalancedBohrShape.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/UnbalancedBohrShape.lean#L287

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

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

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_bohr_second_moment_at_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ S.carrier ∧ C.carrier ⊆ (S.ndilate kappa).carrier ∧
      (C.rank : ℝ) ≤ S.rank + almostPeriodicityWidthConstant (c / 64) * (1 + D) ^ 4 ∧
      ((kappa : ℝ) * (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) * S.radius / 8) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ C.radius ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  sorry

end Erdos3.LocalConvolution
end
end OAI
