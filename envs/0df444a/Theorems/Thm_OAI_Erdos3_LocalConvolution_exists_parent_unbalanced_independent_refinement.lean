-- Prove2me | Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_parent_unbalanced_independent_refinement
-- name    : OAI.Erdos3.LocalConvolution.exists_parent_unbalanced_independent_refinement
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:27.522905+00:00
-- url     : https://prove2.me/theorems/94e7bf02-209f-4961-93e4-c845933035bf
-- title:
--   A large difference moment yields an admissible cell with a quarter-power density drop
-- statement:
--   Let $N$ be a positive natural number (`[NeZero N]`). A `CyclicBohr.Set N` is OpenAI's structure bundling a finite set of frequencies in $\mathbb{Z}/N$ and a radius $\rho \ge 0$; its `carrier` is the finite set of $x$ with $\|1 - \chi_r(x)\| \le \rho$ for every frequency $r$ ($\chi_r$ the additive character `CyclicBohr.character r`), its `rank` is the number of frequencies, `ndilate t` scales the radius by $t \in \mathbb{R}_{\ge 0}$, and `IsRankRegular` is OpenAI's regularity predicate on carrier sizes of the dilates by $1 \pm \kappa$; below a Bohr set stands for its carrier where a set is meant. `Peeling.admissibleBohrShape B scale extra w C` is the predicate: $C$ is rank-regular, $C \subseteq$ `B.ndilate scale`, $\operatorname{rank} C \le \operatorname{rank} B + \mathrm{extra}$ and $w \le \rho_C$.
--
--   Let $B, L, S$ be Bohr sets with $L$ rank-regular, $0 < \rho_S \le 1$, $S$ rank-regular, $1 \le \operatorname{rank} S$, $S$ with the same frequencies as $L$, and $\rho_S \le \rho_L$. Let $\kappa, \mathrm{scale} \in \mathbb{R}_{\ge 0}$, $\mathrm{extra} \in \mathbb{N}$ and $w_{\min}, c, p, H, W, A, E \in \mathbb{R}$, with $S \subseteq$ `L.ndilate κ`, $\kappa + \kappa \le 1/(100 \cdot 2\max(\operatorname{rank} L,1))$, $S \subseteq$ `B.ndilate scale`, $\operatorname{rank} S + $ `unbalancedRankExtra c p H` $\le \operatorname{rank} B + \mathrm{extra}$, and $w_{\min} \le \rho_S \exp(-$`unbalancedReturnWidthLoss (rank S) c p H A E`$)$ (`unbalancedRankExtra` is a natural number and `unbalancedReturnWidthLoss` a real, both explicit functions of OpenAI). Let $F, G, f, g : \mathbb{Z}/N \to \mathbb{R}$ and $x, y \in \mathbb{Z}/N$ with $f(r) \le F(x+r)$ and $g(r) \le G(y+r)$ for all $r$, $0 \le f, g \le 1$ pointwise, and $f, g$ vanishing off $L$. Let $U, V, u, v, M, K, c_0$ be reals with $0 < U$, $0 < V$, $0 < c_0$, $0 \le K$, $c_0 U \le u$, $c_0 V \le v$, $\mathbb{E}_{r \in L} f(r) \le u$ and $\mathbb{E}_{r \in L} g(r) \le v$; suppose that for every Bohr set $C$ with `Peeling.admissibleBohrShape B scale extra w_min C` and every $z$, `cellAverage C F z` $\le K U$ and `cellAverage C G z` $\le K V$ (where `cellAverage C F z` $= \mathbb{E}_{t \in C} F(z+t)$). Suppose further $0 < M$, $0 < c \le 1$, $1 \le p$, $0 \le H$, $M \le e^{p}$, $f(r)/u \le M$ and $g(r)/v \le M$ for all $r$, and $M^2 (400 \max(\operatorname{rank} L, 1)(\kappa+\kappa)) \le c/32$. Let $q$ be a positive even natural number with $q \le H p$, and let $h$ be one of the two functions $r \mapsto f(r)/u$, $r \mapsto g(r)/v$, with $1 + c \le$ `differenceLp S (correlation L h h) q` (the $L^q$ average $(\mathbb{E}_{(s,t) \in S \times S} |\phi(s-t)|^q)^{1/q}$ of $\phi = $ `correlation L h h`, $\phi(t) = \sum_x h(x+t) h(x) / |L|$), and $(1 + c/4)^q \le \tfrac{c/64}{2} (1 + c/2)^q$. Finally let $0 \le W \le e^{A}$, $0 \le A$ and $0 \le E$.
--
--   Then there is a Bohr set $C$ such that: `Peeling.admissibleBohrShape B scale extra w_min C`; `Peeling.admissibleBohrShape S (CellRefinement.independentReturnScale (rank S) W (exp (-E))) (unbalancedRankExtra c p H) (ρ_S · exp(-unbalancedReturnWidthLoss (rank S) c p H A E)) C` (`independentReturnScale` being an explicit $\mathbb{R}_{\ge 0}$-valued scale of OpenAI); $0 < \rho_C \le 1$; with $\varrho = 1 - c / (128 (1 + \sqrt{K/c_0})^2)$ one has $3/4 \le \varrho < 1$ and
--   $$\mathbb{E}_{z \in L \times S \times S} \bigl(\texttt{matchedFirstCell}\,C\,f\,z \cdot \texttt{matchedSecondCell}\,C\,g\,z\bigr)^{1/4} \le \varrho\,(uv)^{1/4},$$
--   where for $z = (z_1, z_2, z_3)$ the first factor is `cellAverage C f z₁` and the second `cellAverage C g (-z₁ + z₂ + z₃)` (`matchedCellSpace L S` is $L \times S \times S$, and the power is the real power); and for every $a : \mathbb{Z}/N \to \mathbb{R}$ with $|a(r)| \le W$ for all $r$,
--   $$\Bigl|\mathbb{E}_{z \in L \times S \times S}\, \texttt{bilinearIntegral}(z_1 + C,\ (-z_1+z_2+z_3) + C,\ a, f, g) - \texttt{matchedIntegral}(L, S, a, f, g)\Bigr| \le e^{-E},$$
--   where `CellRefinement.bilinearIntegral X Y a f g` is the average over $x \in X$, $y \in Y$ of $f(x) g(y) a(x+y)$, the translates are images of the carrier of $C$, and `CellRefinement.matchedIntegral L S a f g` is the average over $r \in L$, $s, t \in S$ of $f(r)\,g(-r+s+t)\,a(s+t)$.
--
--   Lean: `OAI.Erdos3.LocalConvolution.exists_parent_unbalanced_independent_refinement` in `lean/OAI/Combinatorics/Progressions/Estimates/RefinementMatchingGeometry.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RefinementMatchingGeometry.lean#L523

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

theorem exists_parent_unbalanced_independent_refinement
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H W A E : ℝ}
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E))
    (F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) ≤ u) (hmeang : (𝔼 r ∈ L.carrier, g r) ≤ v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun r => f r / u) ∨ h = (fun r => g r / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S
        (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - c / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ r, |a r| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            CellRefinement.bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          CellRefinement.matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  sorry

end Erdos3.LocalConvolution
end
end OAI
