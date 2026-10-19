-- Prove2me | Theorems.Thm_OAI_Erdos3_positiveAffineModerate_grid_approximation_on_cover_s2
-- name    : OAI.Erdos3.positiveAffineModerate_grid_approximation_on_cover_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:26:16.801466+00:00
-- url     : https://prove2.me/theorems/906695c9-a82f-4298-b455-60b81d0b293a
-- title:
--   The integer grid density of a positive affine moderate jet sum is approximated by a Fourier sum over a small spectrum cover
-- statement:
--   Let $B$ and $I$ be finite types with decidable equality and $n$ a natural number. Let $c_b$, for $b \in B$, be a `NormalizedScalarCubeSource Empty`, and $s_{b,j}$, for $b \in B$ and $j \in \operatorname{Fin}(n+1)$, a `NormalizedScalarCubeSource I` (OpenAI's structure: a positive length, moduli and residues on $\mathrm{Option}$ of the index type bounded by a modulus bound, a size condition, and a probability weight `source` on the integer cube box of that length). Let $u : B \to \operatorname{Fin}(n+1) \to \mathrm{Option}\ I \to \mathbb{Z}$ and $v : B \to \operatorname{Fin}(n+1) \to \mathrm{Option}\ I \to \mathbb{N}$. Let $A \in \mathbb{R}_{\ge 0}$ with Mathlib's `Real.smoothTransition` $A$-Lipschitz, and let $U, V, W, L, \varepsilon$ be reals. Assume:
--   - $U \ge 1$; `ScalarCubePrimitiveBudget (c b) A U` for every $b$ and `ScalarCubePrimitiveBudget (s b j) A U` for all $b, j$ (OpenAI's predicate: $U$ bounds the dimension plus one, the modulus bound, the weight bound and its Lipschitz constant, and several cube boundary and cutoff constants);
--   - $v_{b,j}(i) > 0$ and $v_{b,j}(i) \cdot (s_{b,j}.\texttt{modulus})(i) \le U$ for all $b, j, i$;
--   - (hpositive) for every $b$ and every cube point $z$ with $(c_b.\texttt{source}).\texttt{weight}(z) \ne 0$, one has $c_b.\texttt{length}/4 \le z(\texttt{none})$;
--   - $V \ge 0$, $W \ge 0$, $L \ge 0$, $0 < \varepsilon \le 1$, and $L \le s_{b,j}.\texttt{length}$ for all $b, j$;
--   - natural numbers $K, M, t$ with $M \ne 0$ and $M / (c_b.\texttt{length} \cdot \prod_j s_{b,j}.\texttt{length}) \le V$ for every $b$;
--   - a finite set $J$ of finite subsets of $I$, each of size at most $n+1$, with `positiveModerateSpectrumBlockCount n |J| t` $\le |B|$ (an explicit natural number of OpenAI) and $M^{|J|} \le W L^t$.
--
--   Let $F$ = `positiveModerateSpectrumCover J M n U V L (positiveModerateRetainedBias n |J| t U V W ε)`, OpenAI's explicit finite set of frequency vectors $J \to \operatorname{Fin} M$. Then $|F| \le$ `positiveModerateSpectrumCardBudget n |J| t U V W ε` (an explicit real number of OpenAI), and for all $\mathrm{shift}, z : J \to \mathbb{Z}$,
--   $$\Bigl\lVert \texttt{integerGridDensity}(P, Y, K, M, z) - \texttt{weightedAffineModerateGridApproximation c s u v K M J 0 shift z } F \Bigr\rVert \le \Bigl(\frac{K}{M}\Bigr)^{|J|} \varepsilon,$$
--   where $P$ = `weightedModerateIntegerProductSource c s` (the product over $b$ of OpenAI's weighted moderate integer sources), $Y$ = `weightedAffineModerateIntegerJetSum c s u v J 0 shift` (the vector $\mathrm{shift} + \sum_b$ of OpenAI's affine moderate integer blocks, with all offsets $0$), `integerGridDensity P Y K M z` $= K^{|J|}$ times OpenAI's grid mass of $Y$ at $z$ modulo $M$ (a real number, here viewed as complex), and `weightedAffineModerateGridApproximation … F` $= (K/M)^{|J|} \sum_{k \in F} \bigl(\prod_b \text{(OpenAI's grid coefficient of block } b \text{ at } k)\bigr) \chi_k(\mathrm{shift}) \overline{\chi_k(z)}$ with $\chi_k$ OpenAI's rectangular grid character modulo $M$.
--
--   Lean: `OAI.Erdos3.positiveAffineModerate_grid_approximation_on_cover_s2`, which states OpenAI's `OAI.Erdos3.positiveAffineModerate_grid_approximation_on_cover` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueGrid.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B150` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedSlicedResidueGrid.lean (declaration OAI.Erdos3.positiveAffineModerate_grid_approximation_on_cover)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem positiveAffineModerate_grid_approximation_on_cover_s2
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M]
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) :
    let F := positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n J.card t U V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget n J.card t U V W ε ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
            (weightedAffineModerateIntegerJetSum c s u v J (fun _ => 0) shift) K M z : ℂ) -
          weightedAffineModerateGridApproximation c s u v K M J (fun _ => 0) shift z F‖ ≤
            ((K : ℝ) / M) ^ J.card * ε := by
  sorry

end Erdos3

end

end OAI
end
