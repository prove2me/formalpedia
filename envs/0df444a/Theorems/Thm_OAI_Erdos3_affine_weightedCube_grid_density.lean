-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_weightedCube_grid_density
-- name    : OAI.Erdos3.affine_weightedCube_grid_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T13:31:49.015899+00:00
-- url     : https://prove2.me/theorems/201661cf-5c30-4956-af48-87d2e2924537
-- title:
--   Grid density of an affine weighted-cube integer sum is close to its spectral approximation
-- statement:
--   Let $B$ and $I$ be finite types with decidable equality and $n\in\mathbb N$. For each $b\in B$ and $j\in\mathrm{Fin}(n+1)$ let $s_{b,j}$ be a `NormalizedScalarCubeSource I` (a structure bundling a length $\ell>0$, a modulus bound, moduli $m_i>0$ and residues for $i\in\mathrm{Option}\,I$, and a bounded Lipschitz weight, normalized so that it determines a probability law `source` on `IntegerScalarCubeBox I ℓ`), $u_{b,j}\colon\mathrm{Option}\,I\to\mathbb Z$ and $v_{b,j}\colon\mathrm{Option}\,I\to\mathbb N$. Let $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz, and reals $U,V,W,L,\varepsilon$ with $1\le U$, $0\le V$, $0\le W$, $0\le L$, $0<\varepsilon$. Assume `ScalarCubePrimitiveBudget (s b j) A U` for all $b,j$ (a predicate bounding $|I|+1$, the modulus bound, the weight bound, the weight's Lipschitz constant and two boundary constants of the scalar cube by $U$); $L\le\ell(s_{b,j})$; $v_{b,j}(i)>0$ and $v_{b,j}(i)\,m_i(s_{b,j})\le U$ for all $b,j,i$. Let $K,M,t\in\mathbb N$ with $M\ne0$, and let $J$ be a finite family of finite subsets of $I$ each of size at most $n+1$, with `uniformSpectrumBlockCount n |J| t` $\le|B|$, $M^{|J|}\le WL^t$, and $M/\prod_j\ell(s_{b,j})\le V$ for every $b$. Put $\zeta=$ `uniformBlockRetainedBias n |J| t U V W ε` and $S=$ `uniformBlockSpectrumCover J M n U V L ζ` (a finite set of frequencies $J\to\mathrm{Fin}\,M$). Then for every $\mathrm{shift}\colon J\to\mathbb Z$ and every $z\colon J\to\mathbb Z$,
--   $$\big|\texttt{integerGridDensity}\ p\ Y\ K\ M\ z-\texttt{integerGridApproximation}\ p\ Y\ K\ M\ S\ z\big|\le (K/M)^{|J|}\,\varepsilon,$$
--   where $p=$ `weightedCubeIntegerSource s` is the product over $b,j$ of the laws `(s b j).source`, and $Y=$ `affineWeightedCubeIntegerSum s u v J shift` is the random vector $\mathrm{shift}+\sum_b(\text{block jets})$ in $\mathbb Z^J$ whose $b$-th term `affineWeightedCubeIntegerBlock` takes, for each $T\in J$, the Boolean coefficient at $T$ (`integerBooleanBlockJet`) of the affine integer coordinates $i\mapsto u_{b,j}(i)+v_{b,j}(i)\,x_{b,j}(i)$. `integerGridDensity p Y K M z` is $K^{|J|}$ times the $p$-probability that $Y\equiv z\pmod M$ coordinatewise, and `integerGridApproximation p Y K M S z` is $(K/M)^{|J|}\sum_{k\in S}\hat p(k)\,\overline{\chi_k(z)}$, with $\chi_k$ the character `rectangularGridCharacter M k` of $(\mathbb Z/M)^J$ and $\hat p(k)$ the $p$-mean of $\chi_k(Y)$ (`integerGridCoefficient`). `uniformSpectrumBlockCount` and `uniformBlockRetainedBias` are OpenAI's explicit numerical parameters.
--
--   Lean: `OAI.Erdos3.affine_weightedCube_grid_density` in `lean/OAI/Combinatorics/Progressions/Lattices/WeightedSliceIntegerImage.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B088` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/WeightedSliceIntegerImage.lean#L19

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_grid_density {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (K M t : ℕ) [NeZero M] (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    ∀ shift z, ‖(integerGridDensity (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
      K M z : ℂ) - integerGridApproximation (weightedCubeIntegerSource s) (affineWeightedCubeIntegerSum s u v J shift)
        K M S z‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  sorry

end Erdos3
end
end OAI
